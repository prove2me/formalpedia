-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:00.136944+00:00
-- url     : https://prove2.me/submissions/a8ea5320-2f8a-4072-a56b-419287e373d8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {n : ℕ} {x : Γ} (h : T.π * x ∈ Ideal.span {T.π ^ (n + 1)}) :
    x ∈ Ideal.span {T.π ^ n} := by
  obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
  refine T.mem_span_pow.2 ⟨y, T.π_mul_cancel ?_⟩
  rw [hy, pow_succ]; ring
end GroundTheory.PAdicHodge.TeichLift
