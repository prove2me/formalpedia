-- Prove2me | solution 1 for PI.WeylForUWork.denom_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:23.584796+00:00
-- url     : https://prove2.me/submissions/58e64383-745f-461f-870c-860d8a7e4913

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions
namespace PI.WeylForUWork
theorem _root_.solution (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) (n + 1), ((j : ℝ) - (i : ℝ)) =
        (∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) * ((n : ℝ) - (i : ℝ)) := by
      intro i hi
      exact Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) _
    have h2 : ∀ k : ℕ, ∏ i ∈ range k, ((k : ℝ) - (i : ℝ)) = ((k.factorial : ℕ) : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        have e : ∀ i ∈ range k, (((k + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) = (k : ℝ) - (i : ℝ) := by
          intro i _
          push_cast
          ring
        rw [Finset.prod_range_succ', Finset.prod_congr rfl e, ihk, Nat.factorial_succ]
        push_cast
        ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
      Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ih, h2 n]
end PI.WeylForUWork
