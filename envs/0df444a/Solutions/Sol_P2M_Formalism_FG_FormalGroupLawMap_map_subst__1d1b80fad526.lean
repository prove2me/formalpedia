-- Prove2me | solution 1 for P2M_Formalism_FG_FormalGroupLawMap_map_subst__1d1b80fad526
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:02.696054+00:00
-- url     : https://prove2.me/submissions/5cc62940-8a35-4477-9834-1d547db3b4b3

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupLawMap
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]
namespace Formalism.FG.FormalGroupLawMap
theorem _root_.solution {σ τ : Type*} [Finite σ] (h : R →+* S) {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    map h (subst a f) = subst (fun s => map h (a s)) (map h f) :=
  map_subst (hasSubst_of_constantCoeff_zero ha) f
end Formalism.FG.FormalGroupLawMap
