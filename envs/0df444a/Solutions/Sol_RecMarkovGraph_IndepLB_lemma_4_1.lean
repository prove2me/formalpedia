-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T14:52:32.501167+00:00
-- url     : https://prove2.me/submissions/941d7f6b-b0e8-4752-9e63-aa6a3fae2778

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Set

theorem lemma_4_1 (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ConcaveOn ℝ univ (fa a) ∧
    (StrictMonoOn (fa a) (Iic (1 / (2 * a))) ∧ StrictAntiOn (fa a) (Ioi (1 / (2 * a)))) ∧
    ((∀ x, fa a x ≤ 1 / (4 * a)) ∧ fa a (1 / (2 * a)) = 1 / (4 * a)) ∧
    (∀ x, fa a x = x → x = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, fa a x ∈ Ioo (0 : ℝ) 1) ∧
    (∀ x, x ≠ 0 → fa a x < x) ∧
    (∀ x, a * fa a x = fa 1 (a * x)) ∧
    (∀ b x : ℝ, b < a → 0 < x → fa a x < fa b x) := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  refine ⟨⟨convex_univ, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y _ α β hα hβ hαβ
    simp only [fa, smul_eq_mul]
    have hβ' : β = 1 - α := by linarith
    subst hβ'
    nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (x - y)), ha.le]
  · intro x hx y hy hxy
    simp only [mem_Iic] at hx hy
    have h1 : 2 * a * y ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hy h2a.le
      rwa [mul_one_div_cancel h2a.ne'] at this
    simp only [fa]
    nlinarith [mul_pos (sub_pos.mpr hxy) ha]
  · intro x hx y hy hxy
    simp only [mem_Ioi] at hx hy
    have h1 : 1 < 2 * a * x := by
      have := mul_lt_mul_of_pos_left hx h2a
      rwa [mul_one_div_cancel h2a.ne'] at this
    simp only [fa]
    nlinarith [mul_pos (sub_pos.mpr hxy) ha]
  · intro x
    simp only [fa]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * a)]
    have : x * (1 - a * x) * (4 * a) = 1 - (2 * a * x - 1) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (2 * a * x - 1)]
  · simp only [fa]; field_simp; ring
  · intro x hx
    simp only [fa] at hx
    have : a * x ^ 2 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · intro x hx
    obtain ⟨h0, h1⟩ := hx
    have hax : a * x < 1 := by nlinarith
    simp only [fa]
    constructor
    · exact mul_pos h0 (by linarith)
    · nlinarith [mul_pos ha h0]
  · intro x hx
    simp only [fa]
    have : 0 < x ^ 2 := by positivity
    nlinarith [mul_pos ha this]
  · intro x; simp only [fa]; ring
  · intro b x hb hx
    simp only [fa]
    have : 0 < x ^ 2 := by positivity
    nlinarith [mul_pos (sub_pos.mpr hb) this]

end RecMarkovGraph.IndepLB


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

open Set

theorem _root_.solution (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ConcaveOn ℝ univ (fa a) ∧
    (StrictMonoOn (fa a) (Iic (1 / (2 * a))) ∧ StrictAntiOn (fa a) (Ioi (1 / (2 * a)))) ∧
    ((∀ x, fa a x ≤ 1 / (4 * a)) ∧ fa a (1 / (2 * a)) = 1 / (4 * a)) ∧
    (∀ x, fa a x = x → x = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, fa a x ∈ Ioo (0 : ℝ) 1) ∧
    (∀ x, x ≠ 0 → fa a x < x) ∧
    (∀ x, a * fa a x = fa 1 (a * x)) ∧
    (∀ b x : ℝ, b < a → 0 < x → fa a x < fa b x) := by
  apply @RecMarkovGraph.IndepLB.lemma_4_1 <;> assumption

end RecMarkovGraph.IndepLB
