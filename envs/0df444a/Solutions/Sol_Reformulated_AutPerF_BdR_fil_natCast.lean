-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.fil_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:14:31.856257+00:00
-- url     : https://prove2.me/submissions/36301282-7dd4-4a2f-9874-942431bcde86

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta


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
theorem _root_.solution (n : ℕ) : fil p R n = filNat p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), filNat_eq_span (BdRPlus.ker_theta ϖ), zpow_natCast]
end Reformulated.AutPerF.BdR
