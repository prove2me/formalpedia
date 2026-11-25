-- Prove2me | solution 1 for P2M_HostParam_Seam_Comparison__iso_resMap_e10e06081470
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:06.42087+00:00
-- url     : https://prove2.me/submissions/5cac7f79-1086-449a-9036-d82a5a664c31

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
namespace Comparison₂
theorem _root_.solution {C : Core} {φ : Frame} {H : HostRaw φ} (t : Comparison₂ C H) (u : (ZMod H.condN)ˣ) :
    t.iso (t.resMap u) = H.art u := t.iso.apply_symm_apply _
end Comparison₂
end HostParam.Seam
