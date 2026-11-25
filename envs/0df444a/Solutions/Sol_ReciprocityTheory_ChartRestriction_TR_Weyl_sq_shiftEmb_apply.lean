-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_shiftEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:39.430862+00:00
-- url     : https://prove2.me/submissions/cd133024-1725-4018-81f7-bc410294c26a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {n : ℕ} (c : ℤ) (mu : Fin n → ℤ) : sq_shiftEmb c mu = fun i => mu i + c := rfl
end ReciprocityTheory.ChartRestriction.TR.Weyl
