-- Prove2me | solution 1 for ThreeSum.HashFamily.four_relation_of_mask_ne_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:57.884342+00:00
-- url     : https://prove2.me/submissions/384e1ea5-e7ec-4134-a4f0-1e1c9db2eac1

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_WeightedCache3SUM_Alias_4049c0bb9918328c

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Ring K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) {a b c d : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p + d * oneHot v p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    obtain ⟨i, hi⟩ := hm
    have hf := h (i, false)
    have ht := h (i, true)
    cases hs : s i <;> cases hti : t i <;> cases hu : u i <;> cases hv : v i <;>
      simp_all [oneHot]
  rcases hz with ha | hb | hc | hd
  · have hr := three_relation htu htv huv (a := b) (b := c) (c := d)
      (fun p => by simpa [ha] using h p)
    exact ⟨ha, hr.1, hr.2.1, hr.2.2⟩
  · have hr := three_relation hsu hsv huv (a := a) (b := c) (c := d)
      (fun p => by simpa [hb] using h p)
    exact ⟨hr.1, hb, hr.2.1, hr.2.2⟩
  · have hr := three_relation hst hsv htv (a := a) (b := b) (c := d)
      (fun p => by simpa [hc] using h p)
    exact ⟨hr.1, hr.2.1, hc, hr.2.2⟩
  · have hr := three_relation hst hsu htu (a := a) (b := b) (c := c)
      (fun p => by simpa [hd] using h p)
    exact ⟨hr.1, hr.2.1, hr.2.2, hd⟩
end ThreeSum.HashFamily
