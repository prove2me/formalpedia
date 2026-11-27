-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.iSup_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:29.105865+00:00
-- url     : https://prove2.me/submissions/5eb990b8-f75f-48b0-aba5-59ff881e6e70

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_BdR_exists_mem_fil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdR
theorem _root_.solution : ⨆ i, fil p R i = ⊤ :=
  eq_top_iff.2 fun x _ => let ⟨i, hi⟩ := exists_mem_fil x; Submodule.mem_iSup_of_mem i hi
end Reformulated.AutPerF.BdR
