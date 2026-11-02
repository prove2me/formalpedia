-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.CountPositive.success_exact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:33:35.790977+00:00
-- url     : https://prove2.me/submissions/ab1164c3-c9cf-483e-a96d-d67ca66e4260

import Theorems.Thm_TwoAgentSched_TotalTotal_CountPositive_countBody_success_exact
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.CountPositive

private theorem start_success (s out : Fin 4 → List BSym) (steps : ℕ)
    (h : countPositive.Exec s out steps) (hs : (out 2).head? = some .one) :
    (s 2).head? = some .one := by
  unfold countPositive at h
  cases h with
  | loopFalse ht => exact hs
  | loopTrue ht hb hr =>
    have ht' : ((s 0).head?).isSome = true ∧ (s 2).head? = some .one := by
      simpa [continueTest, Bool.and_eq_true] using ht
    exact ht'.2

private theorem loop_exact (steps : ℕ) : ∀ (input status count : List BSym)
    (out : Fin 4 → List BSym),
    countPositive.Exec (store4 input [] status count) out steps →
    (out 2).head? = some .one → out 0 = [] →
    ∃ xs : List ℕ, input = encNats xs ∧
      out 3 = List.replicate (xs.filter (fun x => x ≠ 0)).length .one ++ count := by
  induction steps using Nat.strong_induction_on with
  | h steps ih =>
    intro input status count out h hs he
    unfold countPositive at h
    cases h with
    | loopFalse ht =>
      have hi : input = [] := by simpa [store4] using he
      subst input
      refine ⟨[], rfl, ?_⟩
      simp [store4]
    | @loopTrue _ _ _ mid _ n m ht hb hr =>
      have hm : (mid 2).head? = some .one := start_success mid out m hr hs
      obtain ⟨x, rest, hi, hmid⟩ := countBody_success_exact input status count mid n hb hm
      subst mid
      obtain ⟨xs, hx, hc⟩ := ih m (by omega) rest (.one :: .one :: status)
        (if x = 0 then count else .one :: count) out hr hs he
      refine ⟨x :: xs, ?_, ?_⟩
      · simpa [encNats, hx] using hi
      · by_cases hz : x = 0
        · simp [hz] at hc ⊢
          exact hc
        · simp [hz] at hc ⊢
          rw [hc, List.replicate_succ]
          have H : ∀ k : ℕ, List.replicate k BSym.one ++ .one :: count =
              .one :: (List.replicate k .one ++ count) := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih => simp [List.replicate_succ, ih]
          exact H _

theorem solution
    (input : List BSym) (out : Fin 4 → List BSym) (steps : ℕ)
    (h : countPositive.Exec (store4 input [] [.one] []) out steps)
    (hs : (out 2).head? = some .one) (he : out 0 = []) :
    ∃ xs : List ℕ, input = encNats xs ∧
      out 3 = List.replicate (xs.filter (fun x => x ≠ 0)).length .one := by
  obtain ⟨xs, hi, ho⟩ := loop_exact steps input [.one] [] out h hs he
  exact ⟨xs, hi, by simpa using ho⟩