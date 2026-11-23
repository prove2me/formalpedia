-- Prove2me | solution 1 for PI.SqfRootShift.W.sum_le_prod_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:27.532068+00:00
-- url     : https://prove2.me/submissions/83e3fe9f-f615-427d-9487-c1b516965413

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have h2 : 2 ≤ f a := hf a (mem_insert_self a s)
    have hs : ∀ i ∈ s, 2 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have ih' := ih hs
    have hP : 0 < ∏ i ∈ s, f i := prod_pos (fun i hi => by have := hs i hi; omega)
    rcases s.eq_empty_or_nonempty with he | ⟨b, hb⟩
    · subst he; simp
    · have hb2 : 2 ≤ ∏ i ∈ s, f i :=
        (hs b hb).trans (Nat.le_of_dvd hP (dvd_prod_of_mem f hb))
      nlinarith
end PI.SqfRootShift.W
