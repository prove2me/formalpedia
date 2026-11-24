-- Prove2me | solution 1 for P2M_GlobalTheory_T_root_exchange__809cf020be98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:02:29.651219+00:00
-- url     : https://prove2.me/submissions/feb721cc-57b9-46e7-b160-5faab9bcec61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_rootExchange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  first | exact @GlobalTheory.CompanionTheory.RootExch.rootExchange | exact GlobalTheory.CompanionTheory.RootExch.rootExchange | (intros; apply GlobalTheory.CompanionTheory.RootExch.rootExchange <;> assumption)
end _root_.GlobalTheory.T
