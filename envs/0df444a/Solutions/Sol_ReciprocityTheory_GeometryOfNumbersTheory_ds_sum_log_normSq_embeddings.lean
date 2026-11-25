-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ds_sum_log_normSq_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:29.178139+00:00
-- url     : https://prove2.me/submissions/e4d3f3bb-3c5f-4aa5-aa55-fd22b36bfe46

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_prod_embeddings_eq_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] [NumberField K]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
