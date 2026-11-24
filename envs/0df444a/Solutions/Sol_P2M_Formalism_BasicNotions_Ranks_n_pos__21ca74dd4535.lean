-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Ranks_n_pos__21ca74dd4535
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:13.592209+00:00
-- url     : https://prove2.me/submissions/c21e9e7e-71d7-4246-9a64-bd56713a289e

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
open Formalism.BasicNotions.Ranks
variable (R : Ranks)
namespace Formalism.BasicNotions.Ranks
theorem _root_.solution : 0 < R.n := by
  show 0 < R.ord
  have h1 := R.m_le_f
  have h2 := R.two_le_m
  omega
end Formalism.BasicNotions.Ranks
