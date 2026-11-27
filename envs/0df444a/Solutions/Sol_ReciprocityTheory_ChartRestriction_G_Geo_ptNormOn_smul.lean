-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ptNormOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:58.417846+00:00
-- url     : https://prove2.me/submissions/da701090-66e8-4af3-bb0d-a29e8156a730

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isHomogeneousP

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
open MvPolynomial
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) {d : ℕ}
    {f : MvPolynomial ι o} (hf : (map σ f).IsHomogeneous d) {c : C} (hc : c ≠ 0) {z : ι → C}
    (hz : z ∈ S) (hcz : c • z ∈ S) : ptNormOn m σ d f (c • z) = ptNormOn m σ d f z := by
  unfold ptNormOn
  rw [eval_smul_of_isHomogeneousP hf, m.smul c z hz hcz, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))
end ReciprocityTheory.ChartRestriction.G.Geo
