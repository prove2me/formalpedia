-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.continuous_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:53.537098+00:00
-- url     : https://prove2.me/submissions/7d2c2a4f-3c3a-4e19-9b43-e6e9e6f87c70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution (q n : ℕ) :
    Continuous fun v : Fin n → Vsp X.dim => (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
  have hc : ∀ (k : Fin n) (i : Idx X.dim), Continuous fun v : Fin n → Vsp X.dim => v k i :=
    fun k i => (EuclideanSpace.proj i).continuous.comp (continuous_apply k)
  have hHC : Continuous fun v : Fin n → Vsp X.dim => HC v v := by
    unfold HC Hf
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun i _ =>
      (hc k i).mul (Complex.continuous_conj.comp (hc k i))
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp hHC)))
end ReciprocityTheory.ChartRestriction.G.I2.PT
