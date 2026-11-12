-- Prove2me | solution 1 for QEC.Distillation.Why24ConstantOverhead.why24CCZCatalyticTBatch_run
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T08:02:51.587191+00:00
-- url     : https://prove2.me/submissions/7ae68c88-53ac-4563-a7c5-8ec097326461

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
set_option autoImplicit false
noncomputable section
open QEC.Distillation.Why24ConstantOverhead

theorem why24CCZCatalyticTBatch_run_gen (batch t : Nat) (ht : 1 ≤ t) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := t, cczCount := batch } =
      some { tCount := t + 2 * batch, cczCount := 0 } := by
  induction batch generalizing t with
  | zero =>
      simp [why24CCZCatalyticTBatch, why24RunConversionProgram]
  | succ n ih =>
      change why24RunConversionProgram (.cczCatalyticT :: why24CCZCatalyticTBatch n)
          { tCount := t, cczCount := n + 1 } =
        some { tCount := t + 2 * (n + 1), cczCount := 0 }
      have step :
          Why24FiniteConversionPrimitive.cczCatalyticT.apply
              { tCount := t, cczCount := n + 1 } =
            some { tCount := t + 2, cczCount := n } := by
        simp [Why24FiniteConversionPrimitive.apply, ht, Nat.succ_le_succ (Nat.zero_le n)]
      simp [why24RunConversionProgram, step, Option.bind]
      have ht' : 1 ≤ t + 2 := by omega
      have h := ih (t + 2) ht'
      have heq : t + 2 + 2 * n = t + 2 * (n + 1) := by omega
      simp [heq] at h
      exact h

theorem solution (batch : Nat) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := 1
          cczCount := batch } =
      some
        { tCount := 2 * batch + 1
          cczCount := 0 } := by
  simpa [Nat.add_comm] using why24CCZCatalyticTBatch_run_gen batch 1 (Nat.le_refl 1)
