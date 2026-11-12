-- Prove2me | solution 1 for QEC.Distillation.Why24ConstantOverhead.why24FourTToCCZBatch_run
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T08:02:51.050242+00:00
-- url     : https://prove2.me/submissions/8e97ce74-d9c3-47c1-8db4-e11bd87def73

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
set_option autoImplicit false
noncomputable section
open QEC.Distillation.Why24ConstantOverhead

theorem why24FourTToCCZBatch_run_gen (batch ccz : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch, cczCount := ccz } =
      some { tCount := 0, cczCount := ccz + batch } := by
  induction batch generalizing ccz with
  | zero =>
      simp [why24FourTToCCZBatch, why24RunConversionProgram]
  | succ n ih =>
      change why24RunConversionProgram (.fourTToCCZ :: why24FourTToCCZBatch n)
          { tCount := 4 * (n + 1), cczCount := ccz } =
        some { tCount := 0, cczCount := ccz + (n + 1) }
      have hle : 4 ≤ 4 * (n + 1) := by omega
      simp [why24RunConversionProgram, Why24FiniteConversionPrimitive.apply, hle]
      have ht : 4 * (n + 1) - 4 = 4 * n := by omega
      simp [ht]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih (ccz + 1)

theorem solution (batch : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch
          cczCount := 0 } =
      some
        { tCount := 0
          cczCount := batch } := by
  simpa using why24FourTToCCZBatch_run_gen batch 0
