-- Prove2me | solution 1 for collatz_smaller_predecessor_twentythree_steps_mod_19683
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:53:44.814869+00:00
-- url     : https://prove2.me/submissions/a7b31ba1-5c13-4e98-850c-54c7f65b15e6

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/- Progression verifier adapted from immiq's Prove2Me submission
   1843fe6d-cde2-4133-a4d5-fcfa32356e48 (Apache-2.0).
   Track the image of an entire arithmetic progression. An even coefficient
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

private theorem predecessorRow (n r s : ℕ) (hr : n % 19683 = r)
    (hs : 0 < s) (hsr : s < r)
    (htrace : traceProgression 23 16384 s = some (19683, r)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[23] k = n := by
  have hn : 19683 * (n / 19683) + r = n := by omega
  refine ⟨16384 * (n / 19683) + s, by omega, by omega, ?_⟩
  exact (traceProgression_sound _ _ _ _ _ htrace _).trans hn

theorem solution (n : ℕ)
    (h : n % 19683 ∈ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[23] k = n := by 
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32
  · exact predecessorRow n _ 127 h1 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 359 h2 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 1151 h3 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 1383 h4 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 1775 h5 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 2119 h6 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 2719 h7 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 2799 h8 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 3303 h9 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 3535 h10 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 3743 h11 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 4007 h12 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 4719 h13 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 4839 h14 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 5311 h15 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 5423 h16 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 5663 h17 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 6255 h18 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 6847 h19 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 7199 h20 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 7783 h21 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 9199 h22 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 9319 h23 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 10143 h24 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 10735 h25 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 11079 h26 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 11679 h27 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 12495 h28 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 12967 h29 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 14271 h30 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 14383 h31 (by decide) (by decide) (by decide)
  · exact predecessorRow n _ 15295 h32 (by decide) (by decide) (by decide)
