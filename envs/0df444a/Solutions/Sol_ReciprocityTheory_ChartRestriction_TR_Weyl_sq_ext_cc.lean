-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:39.79903+00:00
-- url     : https://prove2.me/submissions/633d70ee-2077-451a-8cac-637c5a1773a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a t : Fin k) :
    sq_ext μ g a.castSucc t.castSucc = g a t := by simp [sq_ext]
end ReciprocityTheory.ChartRestriction.TR.Weyl
