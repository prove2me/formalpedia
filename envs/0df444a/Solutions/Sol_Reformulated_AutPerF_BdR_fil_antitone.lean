-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.fil_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:32:11.774212+00:00
-- url     : https://prove2.me/submissions/ecfc50e4-e654-4c77-95b2-465fbd3f3305

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_BdR_mem_fil_iff
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
theorem _root_.solution : Antitone (fil p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  intro i j hij x hx
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  obtain ⟨c, rfl⟩ := (mem_fil_iff h _ _).1 hx
  exact (mem_fil_iff h _ _).2 ⟨BdRPlus.xi ϖ ^ n * c, by
    rw [zpow_add₀ (algebraMap_ne_zero h), map_mul, map_pow, zpow_natCast, mul_assoc]⟩
end Reformulated.AutPerF.BdR
