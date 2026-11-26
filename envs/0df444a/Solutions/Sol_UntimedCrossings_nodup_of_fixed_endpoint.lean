-- Prove2me | solution 1 for UntimedCrossings.nodup_of_fixed_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:09:06.2423+00:00
-- url     : https://prove2.me/submissions/af79ffcd-9276-41e4-b28d-1f94d9553f33

import Definitions.Def_UntimedEndpointExchange

open UntimedCrossings

set_option autoImplicit false

private theorem mem_untimedRecord_visit {S : Type*} (side : S → Bool) (step : S → S)
    (z : S) (T : ℕ) {x : S} (inRecord : x ∈ untimedRecord side step z T) :
    ∃ j, 0 < j ∧ j ≤ T ∧ step^[j] z = x := by
  induction T generalizing z with
  | zero => simp [untimedRecord] at inRecord
  | succ T ih =>
    by_cases crosses : side (step z) ≠ side z
    · rw [untimedRecord,if_pos crosses,List.mem_cons] at inRecord
      rcases inRecord with rfl | tail
      · exact ⟨1,by omega,by omega,by simp⟩
      · obtain ⟨j,pos,bound,visit⟩ := ih (step z) tail
        exact ⟨j+1,by omega,by omega,(Function.iterate_succ_apply step j z).trans visit⟩
    · rw [untimedRecord,if_neg crosses] at inRecord
      obtain ⟨j,pos,bound,visit⟩ := ih (step z) inRecord
      exact ⟨j+1,by omega,by omega,(Function.iterate_succ_apply step j z).trans visit⟩

private theorem periodic_of_eventually_fixed {S : Type*} (step : S → S) (z : S)
    (p T : ℕ) (positive : 0 < p) (periodic : step^[p] z = z)
    (settled : step (step^[T] z) = step^[T] z) : step z = z := by
  have periodicAtMultiple : step^[p*(T+1)] z = z := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed periodic (T+1)
  have after : T ≤ p*(T+1) := calc
    T ≤ T+1 := Nat.le_succ T
    _ = 1*(T+1) := (Nat.one_mul _).symm
    _ ≤ p*(T+1) := Nat.mul_le_mul_right _ positive
  have reached : z = step^[T] z := calc
    z = step^[p*(T+1)] z := periodicAtMultiple.symm
    _ = step^[T] z := by
      rw [show p*(T+1) = (p*(T+1)-T)+T by omega, Function.iterate_add_apply]
      exact Function.iterate_fixed settled _
  calc
    step z = step (step^[T] z) := congrArg step reached
    _ = step^[T] z := settled
    _ = z := reached.symm

private theorem untimedRecord_fixed {S : Type*} (side : S → Bool) (step : S → S)
    (z : S) (fixed : step z = z) (T : ℕ) :
    untimedRecord side step z T = [] := by
  induction T with
  | zero => rfl
  | succ T ih => simp [untimedRecord,fixed,ih]

/-- A deterministic run that reaches a fixed point cannot visit the same
crossing destination twice. This includes a crossing into the final fixed state. -/
theorem solution {S : Type*} (side : S → Bool)
    (step : S → S) (z : S) (T : ℕ)
    (settled : step (step^[T] z) = step^[T] z) :
    (untimedRecord side step z T).Nodup := by
  induction T generalizing z with
  | zero => simp [untimedRecord]
  | succ T ih =>
    rw [Function.iterate_succ_apply] at settled
    have tailNodup := ih (step z) settled
    by_cases crossing : side (step z) ≠ side z
    · rw [untimedRecord,if_pos crossing,List.nodup_cons]
      refine ⟨?_,tailNodup⟩
      intro seenAgain
      obtain ⟨p,positive,_,returns⟩ := mem_untimedRecord_visit side step (step z) T seenAgain
      have fixed := periodic_of_eventually_fixed step (step z) p T positive returns settled
      rw [untimedRecord_fixed side step (step z) fixed] at seenAgain
      exact List.not_mem_nil seenAgain
    · simpa only [untimedRecord,if_neg crossing] using tailNodup

#print axioms solution
