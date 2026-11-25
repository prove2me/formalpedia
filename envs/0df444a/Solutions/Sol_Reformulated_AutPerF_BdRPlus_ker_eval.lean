-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.ker_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:29.789317+00:00
-- url     : https://prove2.me/submissions/79608c1c-5b60-4c6b-b323-2c63f7ec014f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham

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
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution (n : ℕ) : RingHom.ker (eval p R n) = fil p R n := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  ext x
  rw [RingHom.mem_ker, eval_eq_zero_iff ϖ, fil_eq_span ϖ, mem_span_singleton]
end Reformulated.AutPerF.BdRPlus
