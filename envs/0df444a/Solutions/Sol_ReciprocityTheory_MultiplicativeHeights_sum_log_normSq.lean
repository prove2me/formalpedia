-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sum_log_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:33.356901+00:00
-- url     : https://prove2.me/submissions/ae1d28e2-f003-457c-a2bb-8ee04a8e0904

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA

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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) =
      2 * Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hprod : (∏ σ : K →+* ℂ, σ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
    have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h2 : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((Algebra.norm ℚ x : ℚ) : ℂ) := eq_ratCast _ _
    rw [h2] at h1
    rw [h1]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hne : ∀ σ : K →+* ℂ, Complex.normSq (σ x) ≠ 0 := fun σ => by
    rw [Ne, Complex.normSq_eq_zero]
    exact (map_ne_zero σ).mpr hx
  have hN : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => Complex.normSq (σ x)) (fun σ _ => hne σ),
    ← map_prod Complex.normSq (fun σ : K →+* ℂ => σ x) Finset.univ, hprod,
    ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hN hN,
    ← Real.log_abs ((Algebra.norm ℚ x : ℚ) : ℝ)]
  ring
end ReciprocityTheory.MultiplicativeHeights
