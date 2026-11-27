-- Prove2me | solution 1 for UntimedCrossings.mixed_never_accept_of_shared_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:47:04.706654+00:00
-- url     : https://prove2.me/submissions/7d7bbf93-167a-4868-a5e4-a719bd5ac9ba

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

private theorem phasePath_split {S : Type*} {side : S → Bool} {step : S → S}
    {z last : S} {lead tail : List S} {total : ℕ}
    (path : PhasePath side step z (lead ++ tail) total last) :
    ∃ reach remaining middle, PhasePath side step z lead reach middle ∧
      PhasePath side step middle tail remaining last ∧ total = reach+remaining := by
  induction lead generalizing z total with
  | nil => exact ⟨0,total,z,.nil z,path,(Nat.zero_add _).symm⟩
  | cons x lead ih =>
    cases path with
    | @cons z next last rest first later positive ends stays crosses remainder =>
      obtain ⟨reach,remaining,middle,head,tail,sum⟩ := ih remainder
      exact ⟨first+reach,remaining,middle,.cons positive ends stays crosses head,tail,by omega⟩

private theorem phasePath_final {S : Type*} {side : S → Bool} {step : S → S}
    {z last : S} {xs : List S} {total : ℕ} (path : PhasePath side step z xs total last) :
    xs.getLast?.getD z = last := by
  induction path with
  | nil => rfl
  | @cons z next last rest first later positive ends stays crosses remainder ih =>
    cases rest with
    | nil => exact ih
    | cons y ys => exact ih

private theorem accept_persists {S : Type*} {step : S → S} {accept : S → Bool}
    (absorbing : ∀ x, accept x = true → step x = x)
    {z : S} {T future : ℕ} (late : T ≤ future) (hit : accept (step^[T] z) = true) :
    accept (step^[future] z) = true := by
  rw [← Nat.sub_add_cancel late,Function.iterate_add_apply,Function.iterate_fixed (absorbing _ hit)]
  exact hit

private theorem phasePath_has_motion {S : Type*} {side : S → Bool} {step : S → S}
    {z last : S} {xs : List S} {total : ℕ} (path : PhasePath side step z xs total last)
    (notEmpty : xs ≠ []) : 0 < total ∧ ∃ n, side (step^[n] z) ≠ side z := by
  cases path with
  | nil => exact (notEmpty rfl).elim
  | @cons z next last rest first later positive ends stays crosses remainder =>
    exact ⟨by omega,first,by rwa [ends]⟩

private theorem cycle_phase_rejects {S : Type*} {side accept : S → Bool} {step : S → S}
    {z x : S} {lead middle : List S} {reach period : ℕ}
    (headPath : PhasePath side step z (lead ++ [x]) reach x)
    (cycle : PhasePath side step x (middle ++ [x]) period x)
    (absorbing : ∀ y, accept y = true → step y = y) :
    ∀ T, accept (step^[T] z) = false := by
  have repeatAt : step^[period] x = x := phasePath_run cycle
  have motion := phasePath_has_motion cycle (by simp)
  intro T
  apply Bool.eq_false_iff.mpr
  intro yes
  let k := period*(T+1)
  have large : T ≤ k+reach := by
    have mul := Nat.mul_le_mul_right (T+1) (show 1 ≤ period from motion.1)
    rw [Nat.one_mul] at mul
    dsimp [k]
    omega
  have again : step^[k] x = x := by
    change step^[period*(T+1)] x = x
    rw [Function.iterate_mul]
    exact Function.iterate_fixed repeatAt _
  have state : step^[k+reach] z = x := by
    rw [Function.iterate_add_apply,phasePath_run headPath,again]
  have accepted := accept_persists absorbing large yes
  rw [state] at accepted
  obtain ⟨n,moves⟩ := motion.2
  have stationary := Function.iterate_fixed (absorbing x accepted) n
  exact moves (congrArg side stationary)

private theorem repeated_crossing_path_rejects
    {S : Type*} {side accept : S → Bool} {step : S → S}
    {z x last : S} {lead middle : List S} {total : ℕ}
    (path : PhasePath side step z ((lead ++ [x]) ++ (middle ++ [x])) total last)
    (absorbing : ∀ y, accept y = true → step y = y) :
    ∀ T, accept (step^[T] z) = false := by
  obtain ⟨reach,period,entry,head,tail,_⟩ := phasePath_split path
  have entryEq : x = entry := by
    simpa using phasePath_final head
  have endEq : x = last := by
    simpa using phasePath_final tail
  subst entry
  subst last
  exact cycle_phase_rejects head tail absorbing

end UntimedCrossings

open UntimedCrossings

theorem solution {S : Type*} (side accept : S → Bool)
    (A B M N : S → S) (z x : S) (TA TB : ℕ) (lead middle tailA tailB : List S)
    (recordA : untimedRecord side A z TA = ((lead ++ [x]) ++ (middle ++ [x])) ++ tailA)
    (recordB : untimedRecord side B z TB = ((lead ++ [x]) ++ (middle ++ [x])) ++ tailB)
    (agreeM : ∀ y, M y = if side y then B y else A y)
    (agreeN : ∀ y, N y = if side y then A y else B y)
    (fixedA : ∀ y, accept y = true → A y = y)
    (fixedB : ∀ y, accept y = true → B y = y) :
    (∀ T, accept (M^[T] z) = false) ∧ (∀ T, accept (N^[T] z) = false) := by
  obtain ⟨_,_,_,wholeA,_⟩ := untimedRecord_has_path side A z TA
  obtain ⟨_,_,_,wholeB,_⟩ := untimedRecord_has_path side B z TB
  rw [recordA] at wholeA
  rw [recordB] at wholeB
  obtain ⟨_,_,_,prefixA,_,_⟩ := phasePath_split wholeA
  obtain ⟨_,_,_,prefixB,_,_⟩ := phasePath_split wholeB
  obtain ⟨_,_,_,_,mixedM,mixedN⟩ := phase_paths_mix prefixA prefixB agreeM agreeN
  have fixedM (y : S) (yes : accept y = true) : M y = y := by
    simp [agreeM,fixedA y yes,fixedB y yes]
  have fixedN (y : S) (yes : accept y = true) : N y = y := by
    simp [agreeN,fixedA y yes,fixedB y yes]
  exact ⟨repeated_crossing_path_rejects mixedM fixedM,repeated_crossing_path_rejects mixedN fixedN⟩

#print axioms solution
