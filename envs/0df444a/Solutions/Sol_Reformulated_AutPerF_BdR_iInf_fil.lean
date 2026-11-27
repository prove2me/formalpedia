-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.iInf_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:57.942654+00:00
-- url     : https://prove2.me/submissions/8bbd8a8d-db49-4bb0-8ef5-155eb978e1fa

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_BdR_eq_zero_of_forall_mem_fil

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
theorem _root_.solution : ⨅ i, fil p R i = ⊥ :=
  eq_bot_iff.2 fun _ hx => eq_zero_of_forall_mem_fil fun i => (Submodule.mem_iInf _).1 hx i
end Reformulated.AutPerF.BdR
