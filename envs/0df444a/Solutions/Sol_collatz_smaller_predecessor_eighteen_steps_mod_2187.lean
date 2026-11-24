-- Prove2me | solution 1 for collatz_smaller_predecessor_eighteen_steps_mod_2187
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:21:50.30495+00:00
-- url     : https://prove2.me/submissions/1843fe6d-cde2-4133-a4d5-fcfa32356e48

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/- Track the image of an entire arithmetic progression. An even coefficient
   makes parity independent of the parameter. -/
private def traceProgression : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | t + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then traceProgression t (a / 2) (b / 2)
      else traceProgression t (3 * a) (3 * b + 1)
    else none

private theorem traceProgression_sound (t a b u v : ℕ)
    (h : traceProgression t a b = some (u, v)) (q : ℕ) :
    collatzStep^[t] (a * q + b) = u * q + v := by
  induction t generalizing a b with
  | zero =>
    simp [traceProgression] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ t ih =>
    simp only [traceProgression] at h
    split at h
    · rename_i ha
      have ha' : a = 2 * (a / 2) := by omega
      rw [Function.iterate_succ_apply]
      split at h
      · rename_i hb
        have hb' : b = 2 * (b / 2) := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) := by
          calc
            a * q + b = (2 * (a / 2)) * q + 2 * (b / 2) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        rw [hx]
        simpa [collatzStep] using ih _ _ h
      · rename_i hb
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) + 1 := by
          calc
            a * q + b = (2 * (a / 2)) * q + (2 * (b / 2) + 1) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        have hodd : ¬ Even (a * q + b) := by simp [hx]
        rw [collatzStep, if_neg hodd]
        convert ih _ _ h using 2
        ring
    · contradiction

private theorem predecessorRow (n r s : ℕ) (hr : n % 2187 = r)
    (hs : 0 < s) (hsr : s < r)
    (htrace : traceProgression 18 2048 s = some (2187, r)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[18] k = n := by
  have hn : 2187 * (n / 2187) + r = n := by omega
  refine ⟨2048 * (n / 2187) + s, by omega, by omega, ?_⟩
  exact (traceProgression_sound _ _ _ _ _ htrace _).trans hn

theorem solution (n : ℕ)
    (h : n % 2187 ∈ [205, 325, 919, 991, 1000, 1090, 1171, 2170]) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[18] k = n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact predecessorRow n _ 191 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 303 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 859 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 927 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 935 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 1019 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 1095 h (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 2031 h (by decide) (by decide) (by decide)
