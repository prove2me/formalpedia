-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_ll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:59.104813+00:00
-- url     : https://prove2.me/submissions/a0f39b35-ec5e-4c13-b4c9-330d244a60e1

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
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) :
    sq_ext μ g (Fin.last k) (Fin.last k) = (μ (Fin.last k)).toNat := by simp [sq_ext]
end ReciprocityTheory.ChartRestriction.TR.Weyl
