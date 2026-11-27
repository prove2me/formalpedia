-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbamix_logRatio_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:37:07.802451+00:00
-- url     : https://prove2.me/submissions/efc6200f-405f-4222-8587-19fc9074cc18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {m₀ m₁ : ConeMetric ℂ (Ix κ)} (c : Unit → ℂ) (z : Ix κ → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio m₀ m₁ (fun p => c p.1 * z p) = logRatio m₀ m₁ z := by
  have e : (fun p : Ix κ => c p.1 * z p) = c () • z := by
    funext p
    rfl
  unfold logRatio
  rw [e, m₀.smul, m₁.smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 (hc ()))]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
