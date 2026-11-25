-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:56.912831+00:00
-- url     : https://prove2.me/submissions/65a45920-f0ae-49b8-aed2-2b6e14503c33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution {z : V (nd X)} (hz : cpt X (rmul x1' b1) z ∈ ExtFPf.cell D) :
    Φ X b1 D z ∈ OmF X x1' ∧ β X b1 D z ∈ Bor X.Ψ r ∧
      cpt X (rmul x1' b1) z = rmul (cpt X x1' (Φ X b1 D z)) (β X b1 D z) :=
  D.split _ hz.1 hz.2
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
