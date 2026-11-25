-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.TL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:33.059319+00:00
-- url     : https://prove2.me/submissions/9c18cb40-5e3a-497f-836a-5832cf2980d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {σ : Type} [Fintype σ] (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) :
    TL c t N x = ∑ i ∈ range (N + 1),
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] x := by
  rw [TL, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply]
  congr 1
  first
  | exact Module.End.pow_apply _ _ _
  | exact LinearMap.pow_apply _ _ _
  | (rw [Module.End.coe_pow]; rfl)
  | (rw [LinearMap.coe_pow]; rfl)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
