-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.continuousOn_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:22.049423+00:00
-- url     : https://prove2.me/submissions/2f5b67e1-2aa1-4ff0-82ab-76a3644700ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_continuous_secFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) {n r : ℕ}
    (b : Fin r → MvPolynomial (Ix κ) ℚ) (c : Fin r → ℂ) :
    ContinuousOn (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  refine ContinuousOn.mul ?_ ?_
  · exact ((continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_secFun (b i))).norm.pow 2).continuousOn
  · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
