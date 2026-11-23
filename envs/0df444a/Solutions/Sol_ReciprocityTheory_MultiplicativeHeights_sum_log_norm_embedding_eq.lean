-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:50.007467+00:00
-- url     : https://prove2.me/submissions/6af759b9-3ffc-430f-8c23-fe2a070a3394

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  classical
  have hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ c
  have h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
    rw [← norm_prod, h2, ← h]
    simp [Complex.norm_ratCast]
  rw [← hprod, Real.log_prod (fun σ _ => hne σ)]
end ReciprocityTheory.MultiplicativeHeights
