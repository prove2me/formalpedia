-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.prod_emb_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:31.747588+00:00
-- url     : https://prove2.me/submissions/f7035541-39c6-4958-91b1-3d4633e43363

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_ExistsRatCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E)
    (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hinj : Function.Injective emb)
    (hagree : ∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E))
    (hcard : Fintype.card S = Module.finrank K E) (z : E) :
    ∏ s, emb s z = φ₀ ((Algebra.norm K z : K) : E) := by
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  let f : S → (E →ₐ[K] ℂ) := fun s =>
    { toRingHom := emb s
      commutes' := fun a => by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        exact hagree s a }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext e
    exact DFunLike.congr_fun hst e
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by rw [AlgHom.card, hcard]⟩
  have h1 := Algebra.norm_eq_prod_embeddings (K := K) (E := ℂ) z
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h1
  calc ∏ s, emb s z = ∏ s, f s z := rfl
    _ = ∏ σ : E →ₐ[K] ℂ, σ z := Fintype.prod_bijective f hbij _ _ (fun _ => rfl)
    _ = _ := h1.symm
end PI.UnitaryGroupMassFormula.ProdUnitInert
