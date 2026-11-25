-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:55.126926+00:00
-- url     : https://prove2.me/submissions/134af87b-95be-4e82-8176-812a59ff2328

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
theorem _root_.solution {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (t : Fin k) :
    sq_ext μ g (Fin.last k) t.castSucc = (μ t.castSucc - ((∑ b, g b t : ℕ) : ℤ)).toNat := by
  simp [sq_ext]
end ReciprocityTheory.ChartRestriction.TR.Weyl
