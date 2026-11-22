-- Prove2me | solution 1 for Reformulated.AutPerF.IsUnitBall.frobenius_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:55.493607+00:00
-- url     : https://prove2.me/submissions/0f5ac45d-1364-4a79-be34-561bc3fd6c2e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Theorems.Thm_Reformulated_AutPerF_IsUnitBall_exists_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Filter Topology
open Reformulated Reformulated.AutPerF
universe u v
open Reformulated.AutPerF.IsUnitBall
variable {C : Type u} [NormedField C] (O : ValuationSubring C) [IsUnitBall O]
variable (p : ℕ)
variable [hp : Fact (‖(p : C)‖ < 1)]
namespace Reformulated.AutPerF.IsUnitBall
theorem _root_.solution [IsAlgClosed C] [Fact p.Prime] :
    Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := exists_pow_eq O x (Fact.out : p.Prime).pos
  exact ⟨Ideal.Quotient.mk _ y, by rw [frobenius_def, map_pow]⟩
end Reformulated.AutPerF.IsUnitBall
