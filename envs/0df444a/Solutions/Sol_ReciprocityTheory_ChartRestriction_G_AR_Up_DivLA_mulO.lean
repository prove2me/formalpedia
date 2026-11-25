-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.mulO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:29.849065+00:00
-- url     : https://prove2.me/submissions/546dde43-66ad-4197-bc6e-83cc0078cb99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by
  subst h
  exact (hf.mul hg).congr_right fun z => (pow_add _ _ _).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
