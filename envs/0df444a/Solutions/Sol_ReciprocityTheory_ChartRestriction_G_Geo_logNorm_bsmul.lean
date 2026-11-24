-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.logNorm_bsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:40.902797+00:00
-- url     : https://prove2.me/submissions/46708d7f-8260-4e57-8db2-44adf11d50d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by
  unfold logNorm
  rw [eval_bsmul_of_isMultiHomog hs]
  have hh : A.h (bsmul c z) = (∏ k, ‖c k‖ ^ (a k)) * A.h z := by
    rw [show bsmul c z = fun p => c p.1 * z p from rfl, A.smul c z hc]
    simp [hA, zpow_natCast]
  rw [hh, norm_mul, norm_prod]
  simp only [norm_pow]
  rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]
end ReciprocityTheory.ChartRestriction.G.Geo
