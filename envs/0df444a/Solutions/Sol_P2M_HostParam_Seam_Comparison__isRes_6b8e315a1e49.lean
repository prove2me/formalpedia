-- Prove2me | solution 1 for P2M_HostParam_Seam_Comparison__isRes_6b8e315a1e49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:31.157717+00:00
-- url     : https://prove2.me/submissions/1dc42ee8-261e-4ca1-be34-33bd196f1a43

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective
import Theorems.Thm_P2M_HostParam_Seam_Comparison__iso_resMap_e10e06081470

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
theorem _root_.solution {C : Core} {φ : Frame} {H : HostRaw φ} (t : Comparison₂ C H) : IsRes C.E t.resMap := fun a h h' =>
  t.iso.injective ((t.iso_resMap _).trans (t.art_res a h h'))
end Comparison₂
end HostParam.Seam
