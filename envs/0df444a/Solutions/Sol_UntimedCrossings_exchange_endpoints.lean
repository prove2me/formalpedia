-- Prove2me | solution 1 for UntimedCrossings.exchange_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T21:56:28.38635+00:00
-- url     : https://prove2.me/submissions/b097f186-99c0-4a88-a23f-4ceafa08880e

import Definitions.Def_UntimedEndpointExchange

set_option autoImplicit false

namespace UntimedCrossings

/-- A list of completed crossings, with the total number of steps up
to and including the last crossing. Each phase reads only its starting side. -/
inductive PhasePath {S : Type*} (side : S → Bool) (step : S → S) :
    S → List S → ℕ → S → Prop
  | nil (z : S) : PhasePath side step z [] 0 z
  | cons {z next last : S} {rest : List S} {duration elapsed : ℕ}
      (positive : 0 < duration)
      (ends : step^[duration] z = next)
      (stays : ∀ s < duration, side (step^[s] z) = side z)
      (crosses : side next ≠ side z)
      (remaining : PhasePath side step next rest elapsed last) :
      PhasePath side step z (next :: rest) (duration+elapsed) last

/-- Agreement at each visited state suffices to replay a bounded run. -/
theorem iterate_agrees_while {S : Type*} (f g : S → S) (z : S) (n : ℕ)
    (agrees : ∀ j < n, f (f^[j] z) = g (f^[j] z)) :
    f^[n] z = g^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier : ∀ j < n, f (f^[j] z) = g (f^[j] z) :=
      fun j hj => agrees j (hj.trans (Nat.lt_succ_self n))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih earlier,
      agrees n (Nat.lt_succ_self n)]

/-- A phase path gives the endpoint of the run at its total elapsed time. -/
theorem phasePath_run {S : Type*} {side : S → Bool} {step : S → S} {z last : S}
    {xs : List S} {elapsed : ℕ} (path : PhasePath side step z xs elapsed last) :
    step^[elapsed] z = last := by
  induction path with
  | nil => rfl
  | @cons z next last rest duration elapsed positive ends stays crosses remaining ih =>
    rw [Nat.add_comm duration elapsed, Function.iterate_add_apply, ends, ih]

private theorem cons_of_agrees {S : Type*} {side : S → Bool} {f g : S → S}
    {z next last : S} {rest : List S} {duration elapsed : ℕ}
    (positive : 0 < duration) (ends : f^[duration] z = next)
    (stays : ∀ j < duration, side (f^[j] z) = side z) (crosses : side next ≠ side z)
    (remaining : PhasePath side g next rest elapsed last)
    (agrees : ∀ x, side x = side z → f x = g x) :
    PhasePath side g z (next :: rest) (duration + elapsed) last := by
  have replay (n : ℕ) (within : n ≤ duration) : f^[n] z = g^[n] z :=
    iterate_agrees_while f g z n fun j hj => agrees _ (stays j (hj.trans_le within))
  refine .cons positive ((replay duration le_rfl).symm.trans ends) ?_ crosses remaining
  intro j hj
  rw [← replay j hj.le]
  exact stays j hj

private theorem phasePath_uncons {S : Type*} {side : S → Bool} {step : S → S}
    {z next last : S} {rest : List S} {elapsed : ℕ}
    (path : PhasePath side step z (next :: rest) elapsed last) :
    ∃ first later : ℕ, elapsed = first + later ∧ 0 < first ∧
      step^[first] z = next ∧ (∀ j < first, side (step^[j] z) = side z) ∧
      side next ≠ side z ∧ PhasePath side step next rest later last := by
  cases path with
  | cons positive ends stays crosses remaining =>
    exact ⟨_, _, rfl, positive, ends, stays, crosses, remaining⟩

/-- Mixing two paths with the same untimed crossing record preserves the sum of arrival times. -/
theorem phase_paths_mix {S : Type*} {side : S → Bool} {A B M N : S → S}
    {z lastA lastB : S} {xs : List S} {a b : ℕ}
    (pA : PhasePath side A z xs a lastA) (pB : PhasePath side B z xs b lastB)
    (agreeM : ∀ x, M x = if side x then B x else A x)
    (agreeN : ∀ x, N x = if side x then A x else B x) :
    lastA = lastB ∧ ∃ ma mb : ℕ, ma + mb = a + b ∧
      PhasePath side M z xs ma lastA ∧ PhasePath side N z xs mb lastA := by
  induction pA generalizing b lastB with
  | nil z =>
    cases pB
    exact ⟨rfl, 0, 0, rfl, .nil z, .nil z⟩
  | @cons z next lastA rest firstA laterA positiveA endsA staysA crosses remainingA ih =>
    obtain ⟨firstB, laterB, b_eq, positiveB, endsB, staysB, _, remainingB⟩ :=
      phasePath_uncons pB
    obtain ⟨last_eq, ma, mb, times, mixedM, mixedN⟩ := ih remainingB
    cases direction : side z
    · refine ⟨last_eq, firstA + ma, firstB + mb, by omega, ?_, ?_⟩
      · exact cons_of_agrees positiveA endsA staysA crosses mixedM fun x same => by
          simpa [same.trans direction] using (agreeM x).symm
      · exact cons_of_agrees positiveB endsB staysB crosses mixedN fun x same => by
          simpa [same.trans direction] using (agreeN x).symm
    · refine ⟨last_eq, firstB + ma, firstA + mb, by omega, ?_, ?_⟩
      · exact cons_of_agrees positiveB endsB staysB crosses mixedM fun x same => by
          simpa [same.trans direction] using (agreeM x).symm
      · exact cons_of_agrees positiveA endsA staysA crosses mixedN fun x same => by
          simpa [same.trans direction] using (agreeN x).symm

private theorem prepend_same_side {S : Type*} (side : S → Bool) (step : S → S)
    (z : S) (T : ℕ) (history : List S) (used : ℕ) (last : S)
    (adjacent : side (step z) = side z)
    (bounded : used ≤ T) (path : PhasePath side step (step z) history used last)
    (quiet : ∀ s < T-used, side (step^[s] last) = side last) :
    ∃ extended endState, extended ≤ T+1 ∧ PhasePath side step z history extended endState ∧
      (∀ s < T+1-extended, side (step^[s] endState) = side endState) := by
  cases path with
  | nil =>
    refine ⟨0,z,Nat.zero_le _,PhasePath.nil z,?_⟩
    intro s early
    cases s with
    | zero => rfl
    | succ s =>
      rw [Function.iterate_succ_apply]
      exact (quiet s (by omega)).trans adjacent
  | @cons source next last rest duration elapsed positive ends stays crosses remaining =>
    have sameEnd : step^[duration+1] z = next :=
      (Function.iterate_succ_apply step duration z).trans ends
    have sameSide (s : ℕ) (early : s < duration+1) : side (step^[s] z) = side z := by
      cases s with
      | zero => rfl
      | succ s =>
        rw [Function.iterate_succ_apply]
        exact (stays s (by omega)).trans adjacent
    have crossing : side next ≠ side z := fun same => crosses (same.trans adjacent.symm)
    refine ⟨duration+1+elapsed,last,by omega,?_,?_⟩
    · exact PhasePath.cons (Nat.zero_lt_succ _) sameEnd sameSide crossing remaining
    · intro s early
      exact quiet s (by omega)

/-- The concrete crossing record has a path whose remaining run stays on the
last side up to the simulation horizon. -/
theorem untimedRecord_has_path {S : Type*} (side : S → Bool) (step : S → S)
    (z : S) (T : ℕ) :
    ∃ used last, used ≤ T ∧ PhasePath side step z (untimedRecord side step z T) used last ∧
      (∀ s < T-used, side (step^[s] last) = side last) := by
  induction T generalizing z with
  | zero =>
    refine ⟨0,z,Nat.le_refl _,PhasePath.nil z,?_⟩
    intro s early
    omega
  | succ T ih =>
    obtain ⟨used,last,bounded,path,quiet⟩ := ih (step z)
    by_cases crosses : side (step z) ≠ side z
    · rw [untimedRecord,if_pos crosses]
      refine ⟨1+used,last,by omega,?_,?_⟩
      · apply PhasePath.cons (duration := 1) (by decide) (Function.iterate_one step ▸ rfl) _ crosses path
        intro s early
        have atStart : s = 0 := by omega
        subst s
        rfl
      · intro s early
        exact quiet s (by omega)
    · rw [untimedRecord,if_neg crosses]
      exact prepend_same_side side step z T _ used last (not_ne_iff.mp crosses) bounded path quiet

private theorem replay_final_phase {S : Type*} (side : S → Bool) (A M : S → S)
    (z handoff : S) (original mixed elapsed : ℕ) (enough : original ≤ elapsed)
    (cutA : A^[original] z = handoff) (cutM : M^[mixed] z = handoff)
    (stays : ∀ j < elapsed-original, side (A^[j] handoff) = side handoff)
    (sameSide : ∀ x, side x = side handoff → M x = A x) :
    M^[elapsed-original+mixed] z = A^[elapsed] z := by
  have replay : A^[elapsed-original] handoff = M^[elapsed-original] handoff :=
    iterate_agrees_while A M handoff _ fun j before => (sameSide _ (stays j before)).symm
  calc
    _ = M^[elapsed-original] handoff := by rw [Function.iterate_add_apply,cutM]
    _ = A^[elapsed-original] handoff := replay.symm
    _ = A^[elapsed-original+original] z := by rw [Function.iterate_add_apply,cutA]
    _ = _ := by rw [Nat.sub_add_cancel enough]

end UntimedCrossings

open UntimedCrossings

theorem solution {S : Type*} (side : S → Bool)
    (A B M N : S → S) (z : S) (stepsA stepsB : ℕ)
    (records : untimedRecord side A z stepsA = untimedRecord side B z stepsB)
    (agreeM : ∀ x, M x = if side x then B x else A x)
    (agreeN : ∀ x, N x = if side x then A x else B x) :
    ∃ m n : ℕ, m+n = stepsA+stepsB ∧
      ((M^[m] z = A^[stepsA] z ∧ N^[n] z = B^[stepsB] z) ∨
       (M^[m] z = B^[stepsB] z ∧ N^[n] z = A^[stepsA] z)) := by
  obtain ⟨ta,lastA,fitA,pathA,quietA⟩ := untimedRecord_has_path side A z stepsA
  obtain ⟨tb,lastB,fitB,pathB,quietB⟩ := untimedRecord_has_path side B z stepsB
  rw [← records] at pathB
  obtain ⟨same,tm,tn,total,pathM,pathN⟩ := phase_paths_mix pathA pathB agreeM agreeN
  subst lastB
  have endA := phasePath_run pathA
  have endB := phasePath_run pathB
  have endM := phasePath_run pathM
  have endN := phasePath_run pathN
  cases zone : side lastA with
  | false =>
    refine ⟨stepsA-ta+tm,stepsB-tb+tn,by omega,Or.inl ⟨?_,?_⟩⟩
    · apply replay_final_phase side A M z lastA ta tm stepsA fitA endA endM quietA
      intro x sameSide
      simpa [sameSide.trans zone] using agreeM x
    · apply replay_final_phase side B N z lastA tb tn stepsB fitB endB endN quietB
      intro x sameSide
      simpa [sameSide.trans zone] using agreeN x
  | true =>
    refine ⟨stepsB-tb+tm,stepsA-ta+tn,by omega,Or.inr ⟨?_,?_⟩⟩
    · apply replay_final_phase side B M z lastA tb tm stepsB fitB endB endM quietB
      intro x sameSide
      simpa [sameSide.trans zone] using agreeM x
    · apply replay_final_phase side A N z lastA ta tn stepsA fitA endA endN quietA
      intro x sameSide
      simpa [sameSide.trans zone] using agreeN x

#print axioms solution
