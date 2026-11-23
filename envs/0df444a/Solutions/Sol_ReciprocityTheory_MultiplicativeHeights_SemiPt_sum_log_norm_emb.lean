-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.sum_log_norm_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:31.91218+00:00
-- url     : https://prove2.me/submissions/fb37a5d5-349d-497f-b579-a6240177ee3b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] (a : K) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h1 : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
      have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
      simp only [eq_ratCast] at h
      rw [h]
      exact Fintype.prod_bijective (fun σ : K →ₐ[ℚ] ℂ => (σ : K →+* ℂ))
        ⟨fun σ τ h => AlgHom.coe_ringHom_injective h,
          fun τ => ⟨τ.toRatAlgHom, RingHom.ext fun x => rfl⟩⟩ _ _ (fun σ => rfl)
    rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => ‖σ a‖)
      (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ha)), ← norm_prod,
      ← h1]
    first
    | rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    | simp [Complex.norm_ratCast]
    | simp
end ReciprocityTheory.MultiplicativeHeights.SemiPt
