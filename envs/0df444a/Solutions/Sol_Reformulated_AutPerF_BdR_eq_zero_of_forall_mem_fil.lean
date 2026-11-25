-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.eq_zero_of_forall_mem_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:40.327486+00:00
-- url     : https://prove2.me/submissions/c366b5fe-12a6-47cf-94f2-48d2e299dcc4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_BdR_algebraMap_mem_fil_iff
import Theorems.Thm_Reformulated_AutPerF_Ainf_eq_zero_of_forall_xi_pow_dvd


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
theorem _root_.solution {x : BdR p R} (h : ∀ i, x ∈ fil p R i) : x = 0 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  obtain ⟨c, rfl⟩ := (mem_fil_zero_iff x).1 (h 0)
  rw [BdRPlus.eq_zero_of_forall_xi_pow_dvd ϖ (x := c) fun n => ?_, map_zero]
  rw [← mem_span_singleton, ← BdRPlus.fil_eq_span, ← algebraMap_mem_fil_iff]
  exact h n
end Reformulated.AutPerF.BdR
