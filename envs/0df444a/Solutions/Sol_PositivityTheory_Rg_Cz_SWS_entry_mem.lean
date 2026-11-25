-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:41.530818+00:00
-- url     : https://prove2.me/submissions/943daec9-0ca0-4b95-b3be-d71fb7fa5587

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i j : Fin n) :
    (fun k => κ τ k i j) ∈ Submodule.span ℂ (Mono κ H) := by
  classical
  change (fun k => κ τ k i j) ∈ monoAlg hK H
  have hent : ∀ σ ∈ H, ∀ a b : Fin n, (fun k => κ σ k a b) ∈ monoAlg hK H := by
    intro σ hσ a b
    apply Submodule.subset_span
    refine ⟨1, fun _ => σ, 0, fun _ => a, fun _ => b, fun _ => hσ, ?_⟩
    funext k
    simp [mono]
  by_cases hτ : τ ∈ H
  · exact hent τ hτ i j
  · have hσ : bar τ ∈ H := by
      by_contra h
      exact hτ ((hH τ).2 h)
    have hinv : ∀ z : ℤ, (fun k => (κ (bar τ) k).det ^ z) ∈ monoAlg hK H := by
      intro z
      apply Submodule.subset_span
      refine ⟨0, Fin.elim0, Pi.single (bar τ) z, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
      funext k
      symm
      simp only [mono, Fin.prod_univ_zero, mul_one]
      rw [Finset.prod_eq_single (bar τ)]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hadj : (fun k => (κ (bar τ) k).adjugate j i) ∈ monoAlg hK H := by
      have hfun : (fun k => (κ (bar τ) k).adjugate j i) = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℤ) • ∏ r, (fun k => ((κ (bar τ) k).updateRow i (Pi.single j 1)) (p r) r) := by
        funext k
        simp [Matrix.adjugate_apply, Matrix.det_apply, Finset.sum_apply, Finset.prod_apply, Units.smul_def]
      rw [hfun]
      refine Subalgebra.sum_mem _ fun p _ => zsmul_mem (Subalgebra.prod_mem _ fun r _ => ?_) _
      by_cases h : p r = i
      · simp only [h, Matrix.updateRow_self]
        exact Subalgebra.algebraMap_mem (monoAlg hK H) ((Pi.single j (1 : ℂ) : Fin n → ℂ) r)
      · simp only [Matrix.updateRow_ne h]
        exact hent _ hσ _ _
    have hkey : (fun k => κ τ k i j) =
        (fun k => (κ (bar τ) k).det ^ (-1 : ℤ)) * (fun k => (κ (bar τ) k).adjugate j i) := by
      funext k
      have hinvM : (κ (bar τ) k)⁻¹ = (κ (bar τ) k)ᴴ := Matrix.inv_eq_right_inv (hK.unit (bar τ) k)
      have e1 : κ τ k i j = star (κ (bar τ) k i j) := by
        have := hK.conj (bar τ) k i j
        rwa [hK.invol] at this
      have e2 : star (κ (bar τ) k i j) = ((κ (bar τ) k)ᴴ) j i := by
        simp [Matrix.conjTranspose_apply]
      rw [Pi.mul_apply, e1, e2, ← hinvM]
      simp [Matrix.inv_def, Ring.inverse_eq_inv', _root_.zpow_neg_one]
    rw [hkey]
    exact Subalgebra.mul_mem _ (hinv (-1)) hadj
end PositivityTheory.Rg.Cz.SWS
