-- Prove2me | solution 1 for PIW.AdelClassFin.stGenusOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:26:36.906819+00:00
-- url     : https://prove2.me/submissions/e4e93ae3-5796-4cfc-919c-9ee147ff7e67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : StGenusOf := by
  intro hD hH I
  classical
  obtain ⟨Λ, hΛ1, hΛ2, hΛ3⟩ := hD I
  obtain ⟨T, hT⟩ := hH I.F I.E I.cm I.n I.J I.J_herm I.J_det
  have huniq : ∀ {g : GL (Fin I.n) I.E} {A B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)},
      IsImg g A B → IsImg g A B' → B = B' := by
    intro g A B B' h h'
    ext v
    exact (h v).trans (h' v).symm
  let rep : Submodule (𝓞 I.E) (Fin I.n → I.E) → I.Gf := fun M₀ =>
    if h : ∃ y, Λ y = M₀ then Classical.choose h else 1
  have hrep : ∀ M₀, (∃ y, Λ y = M₀) → Λ (rep M₀) = M₀ := by
    intro M₀ h
    show Λ (dite _ _ _) = M₀
    rw [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨T.image rep, fun x => ?_⟩
  obtain ⟨hfg, hspan, hsd⟩ := hΛ1 x
  obtain ⟨γ, hγ, M₀, hM₀, himg⟩ := hT (Λ x) hfg hspan hsd
  obtain ⟨c', -, -, hc'⟩ := hΛ3 γ⁻¹ (Subgroup.inv_mem _ hγ)
  have hrange : ∃ y, Λ y = M₀ := by
    refine ⟨c' * x, ?_⟩
    ext v
    rw [hc' x v]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w0, hw0, rfl⟩ := (himg w).1 hw
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hw0
    · intro hv
      refine ⟨(γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, (himg _).2 ⟨v, hv, rfl⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨c, hcG, -, hc⟩ := hΛ3 γ hγ
  have heq : Λ (c * rep M₀) = Λ x := huniq (hc (rep M₀)) (by rw [hrep M₀ hrange]; exact himg)
  obtain ⟨k, hk, hxk⟩ := hΛ2 _ _ heq
  exact ⟨c, hcG, rep M₀, Finset.mem_image_of_mem _ hM₀, k, hk, hxk⟩
end PIW.AdelClassFin
