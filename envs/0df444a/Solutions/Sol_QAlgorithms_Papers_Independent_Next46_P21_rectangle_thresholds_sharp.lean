-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.rectangle_thresholds_sharp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:29:20.192701+00:00
-- url     : https://prove2.me/submissions/8953d8b5-bc0a-49e5-a9f0-143fe3314747

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

theorem g64a_qr (a : Zsqrtd 2) : quadraticReal a = (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 := by
  simp [quadraticReal, Zsqrtd.toReal_apply]

theorem g64a_qrs (a : Zsqrtd 2) : quadraticReal (star a) = (a.re : ℝ) - (a.im : ℝ) * Real.sqrt 2 := by
  rw [g64a_qr]; simp; ring

theorem g64a_mem (x0 x1 y0 y1 : ℝ) (a : Zsqrtd 2) : a ∈ rectangleSolutions x0 x1 y0 y1 ↔
    (x0 ≤ (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 ∧ (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 ≤ x1) ∧
    (y0 ≤ (a.re : ℝ) - (a.im : ℝ) * Real.sqrt 2 ∧ (a.re : ℝ) - (a.im : ℝ) * Real.sqrt 2 ≤ y1) := by
  simp only [rectangleSolutions, Set.mem_ofPred_eq, Set.mem_Icc]; rw [g64a_qr, g64a_qrs]

theorem g64a_s2 : (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.42 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem g64a_L1 : rectangleSolutions 0 1 0 1 = {0, 1} := by
  obtain ⟨h1, h2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  ext ⟨x, y⟩
  rw [g64a_mem]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a1, a2⟩, b1, b2⟩
    have hx0 : (0:ℝ) ≤ x := by linarith
    have hx1 : (x:ℝ) ≤ 1 := by linarith
    have hy0 : (-1:ℝ) < y := by
      by_contra h; push Not at h; nlinarith
    have hy1 : (y:ℝ) < 1 := by
      by_contra h; push Not at h; nlinarith
    have : (0:ℤ) ≤ x := by exact_mod_cast hx0
    have : x ≤ (1:ℤ) := by exact_mod_cast hx1
    have : (-1:ℤ) < y := by exact_mod_cast hy0
    have : y < (1:ℤ) := by exact_mod_cast hy1
    interval_cases x <;> interval_cases y <;> simp [Zsqrtd.ext_iff]
  · rintro (h | h) <;> simp only [Zsqrtd.ext_iff] at h <;> obtain ⟨h, h'⟩ := h <;>
      (try simp at h h') <;> subst h h' <;> norm_num

theorem g64a_L2 : rectangleSolutions 0 (1 + Real.sqrt 2) (-Real.sqrt 2) 1 =
      {0, 1, (⟨0, 1⟩ : Zsqrtd 2), (⟨1, 1⟩ : Zsqrtd 2)} := by
  obtain ⟨h1, h2⟩ := g64a_s2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  ext ⟨x, y⟩
  rw [g64a_mem]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a1, a2⟩, b1, b2⟩
    have hx0 : (-1:ℝ) < x := by linarith
    have hx1 : (x:ℝ) < 2 := by linarith
    have hy0 : (-1:ℝ) < y := by
      by_contra h; push Not at h; nlinarith
    have hy1 : (y:ℝ) < 2 := by
      by_contra h; push Not at h; nlinarith
    have : (-1:ℤ) < x := by exact_mod_cast hx0
    have : x < (2:ℤ) := by exact_mod_cast hx1
    have : (-1:ℤ) < y := by exact_mod_cast hy0
    have : y < (2:ℤ) := by exact_mod_cast hy1
    interval_cases x <;> interval_cases y <;> simp [Zsqrtd.ext_iff] <;> (push_cast at *; nlinarith)
  · rintro (h | h | h | h) <;> simp only [Zsqrtd.ext_iff] at h <;> obtain ⟨h, h'⟩ := h <;>
      (try simp at h h') <;> subst h h' <;> norm_num <;> (try constructor) <;> linarith

theorem solution :
    rectangleSolutions 0 1 0 1 = {0, 1} ∧
    rectangleSolutions 0 (1 + Real.sqrt 2) (-Real.sqrt 2) 1 =
      {0, 1, (⟨0, 1⟩ : Zsqrtd 2), (⟨1, 1⟩ : Zsqrtd 2)} ∧
    ∀ eta : ℝ, 0 < eta →
      rectangleSolutions eta (1 + Real.sqrt 2 - eta) (-Real.sqrt 2 + eta) (1 - eta) = ∅ := by
  refine ⟨g64a_L1, g64a_L2, fun eta heta => ?_⟩
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ha
  have hb : a ∈ rectangleSolutions 0 (1 + Real.sqrt 2) (-Real.sqrt 2) 1 := by
    rw [g64a_mem] at ha ⊢
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := ha
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  rw [g64a_L2] at hb
  rw [g64a_mem] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> norm_num at ha <;> linarith
