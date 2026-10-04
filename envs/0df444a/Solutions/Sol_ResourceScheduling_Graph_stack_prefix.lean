-- Prove2me | solution 1 for ResourceScheduling.Graph.stack_prefix
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:52.467984+00:00
-- url     : https://prove2.me/submissions/885b9c9d-e75f-433a-8bd0-799b9fb56465

import Definitions.Def_ResourceScheduling_Graph_StackPrefix

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {K : Type} [DecidableEq K] (input count : K) (hne : input ≠ count)
    (t : ℕ) (rest : List Letter) (hstop : rest.head? ≠ some .one)
    (s : K → List Letter) (hs : s input = List.replicate t .one ++ rest) :
    (prefixProg input count).Exec s
      (Function.update (Function.update s input rest) count (List.replicate t .one ++ s count))
      (3 * t + 1) := by
  induction t generalizing s with
  | zero =>
    have hf : Function.update (Function.update s input rest) count ([] ++ s count) = s := by
      funext k
      by_cases hk : k = input
      · subst k; simpa [Function.update, hne] using hs.symm
      by_cases hk' : k = count
      · subst k; simp [Function.update]
      · simp [Function.update, hk, hk']
    simp only [List.replicate_zero, Nat.mul_zero, Nat.zero_add, hf]
    exact .loopFalse (by simpa [hs] using hstop)
  | succ t ih =>
    let s' := StackProg.applyAct (prefixAct input count) s
    have hi : s' input = List.replicate t .one ++ rest := by
      simp [s', StackProg.applyAct, prefixAct, StackAct.apply, hs, List.replicate_succ]
    have hc : s' count = .one :: s count := by
      simp [s', StackProg.applyAct, prefixAct, StackAct.apply, Ne.symm hne]
    have he := StackProg.Exec.loopTrue (by simp [hs, List.replicate_succ])
      (StackProg.Exec.act (prefixAct input count) s) (ih s' hi)
    have hf : Function.update (Function.update s' input rest) count (List.replicate t .one ++ s' count) =
        Function.update (Function.update s input rest) count (List.replicate (t + 1) .one ++ s count) := by
      funext k
      by_cases hk : k = input
      · subst k; simp [Function.update, hne]
      by_cases hk' : k = count
      · subst k
        simp [Function.update, hc, List.replicate_succ', List.append_assoc]
      · simp [Function.update, hk, hk', s', StackProg.applyAct, prefixAct, StackAct.apply]
    rw [hf] at he
    convert he using 1 <;> first | rfl | omega

#print axioms solution
