-- Prove2me | solution 1 for Reformulated.AutPerF.IsUnitBall.exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:55.718608+00:00
-- url     : https://prove2.me/submissions/4934ff27-708a-4e3e-9b05-fcc9bf6be4d3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul

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
omit hp
namespace Reformulated.AutPerF.IsUnitBall
theorem _root_.solution [IsAlgClosed C] (x : O) {n : ℕ} (hn : 0 < n) : ∃ y : O, y ^ n = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : C) hn
  refine ⟨⟨y, (mem_iff y).2 ?_⟩, Subtype.ext hy⟩
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg y) hn.ne', ← norm_pow, hy]
  exact norm_le_one x
end Reformulated.AutPerF.IsUnitBall
