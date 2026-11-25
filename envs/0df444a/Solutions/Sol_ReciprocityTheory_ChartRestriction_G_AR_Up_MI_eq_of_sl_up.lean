-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.eq_of_sl_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:38.538826+00:00
-- url     : https://prove2.me/submissions/eb35200e-c9c1-44b6-87e4-87ec8e41aefc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {w w' : Ix ι r → ℂ} (h1 : ∀ τ, sl w τ = sl w' τ) (h2 : ∀ τ, up w τ = up w' τ) : w = w' := by
  funext i
  obtain ⟨τ, a, b⟩ := i
  by_cases hba : b < a
  · have h := congrFun (congrFun (h1 τ) a) b
    simpa [sl, hba] using h
  · have h := congrFun (congrFun (h2 τ) a) b
    simpa [up, hba] using h
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
