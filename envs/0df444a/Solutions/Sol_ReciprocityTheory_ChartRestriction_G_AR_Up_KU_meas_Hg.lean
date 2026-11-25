-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.meas_Hg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:16.136168+00:00
-- url     : https://prove2.me/submissions/294e6e52-1c05-4d74-883c-18ac912bf0fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_cont_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_meas_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_meas_kap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞} (hφ : Measurable φ) (γ : GL (Fin r) E) :
    Measurable (Hg X x0 FF bb φ γ) :=
  ((meas_kap X x0 bb).ennreal_ofReal.mul hφ).indicator ((cont_lact X γ⁻¹).measurable (meas_S X ho hFF))
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
