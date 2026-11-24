-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:43.440849+00:00
-- url     : https://prove2.me/submissions/dcd6c7fd-f089-4ccb-a6aa-3fa6be0e0ac8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
namespace ConeTrdeg
theorem _root_.solution (y : (Σ k, ι k) → Ω) {g : Geo.MRing ι} {d : K → ℕ}
    (hg : Geo.IsMultiHomog g d) :
    Geo.mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  simp only [Geo.mConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [mul_assoc]
  congr 2
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]
end ConeTrdeg
end GroundTheory.Heights₂.Heights
