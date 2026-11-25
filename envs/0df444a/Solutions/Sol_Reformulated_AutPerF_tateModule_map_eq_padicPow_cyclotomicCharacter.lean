-- Prove2me | solution 1 for Reformulated.AutPerF.tateModule.map_eq_padicPow_cyclotomicCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:15.238677+00:00
-- url     : https://prove2.me/submissions/bac3aeb0-adcf-4d92-908d-71e5c7164865

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_Tilt_seq_map
import Theorems.Thm_Reformulated_AutPerF_IsPrimitive_hasEnoughRootsOfUnity
import Theorems.Thm_Reformulated_AutPerF_isPrimitive_eps

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
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Tilt tateModule
variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]
variable [CharZero R]
namespace Reformulated.AutPerF
namespace tateModule
theorem _root_.solution (e : R ≃+* R) (η : tateModule p R) :
    Tilt.map p (e : R →+* R) η.1 = (padicPow η (cyclotomicCharacter R p e)).1 := by
  haveI := (isPrimitive_eps p R).hasEnoughRootsOfUnity
  refine Tilt.ext_seq fun n => ?_
  rw [seq_map, seq_padicPow]
  exact cyclotomicCharacter.spec p e _ (seq_pow_eq_one η n)
end tateModule
end Reformulated.AutPerF
