-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.Gu_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:56.462907+00:00
-- url     : https://prove2.me/submissions/d60992e0-6538-4143-8e93-1132588ded90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_meas_indC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : ContinuousOn P X.dom)
    (hf : ContinuousOn f0 X.dom) (hW : Measurable W) : Measurable (Gu X P f0 W) :=
  ((meas_indC X hP).mul (Complex.continuous_conj.measurable.comp (meas_indC X hf))).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
