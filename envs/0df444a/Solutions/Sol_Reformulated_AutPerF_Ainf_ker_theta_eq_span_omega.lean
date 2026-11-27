-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.ker_theta_eq_span_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:34.911317+00:00
-- url     : https://prove2.me/submissions/a2e126cc-3cfa-436a-9bcc-bb6c8c9d5fc8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta
import Theorems.Thm_Reformulated_AutPerF_Ainf_associated_xi_omega

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
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R] [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution [IsAlgClosed (FractionRing R)] {ε : tateModule p R}
    (hε : IsPrimitive ε) : RingHom.ker (theta p R) = span {omega ε} := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [ker_theta ϖ, Ideal.span_singleton_eq_span_singleton]
  exact associated_xi_omega ϖ hε
end Reformulated.AutPerF.Ainf
