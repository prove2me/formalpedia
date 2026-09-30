-- Prove2me | solution 1 for UnderstandingML.strongly_convex_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:41:28.13537+00:00
-- url     : https://prove2.me/submissions/406229f5-2dc1-4029-9599-3d1ada29377d

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} :
    (∀ lam : ℝ, StrongConvexOn Set.univ (2 * lam) (fun w : Vec d ↦ lam * ‖w‖ ^ 2)) ∧
    (∀ (lam : ℝ) (f g : Vec d → ℝ), StrongConvexOn Set.univ lam f → ConvexOn ℝ Set.univ g →
      StrongConvexOn Set.univ lam (f + g)) ∧
    ∀ (lam : ℝ) (f : Vec d → ℝ) (u : Vec d), StrongConvexOn Set.univ lam f →
      (∀ w, f u ≤ f w) → ∀ w, lam / 2 * ‖w - u‖ ^ 2 ≤ f w - f u := by
  refine ⟨fun lam ↦ ?_, fun lam f g hf hg ↦ ?_, fun lam f u hf hmin w ↦ ?_⟩
  · rw [strongConvexOn_iff_convex]
    have : (fun x : Vec d ↦ lam * ‖x‖ ^ 2 - 2 * lam / 2 * ‖x‖ ^ 2) = fun _ ↦ 0 := by
      funext x; ring
    rw [this]
    exact convexOn_const 0 convex_univ
  · have h := UniformConvexOn.add hf (uniformConvexOn_zero.2 hg)
    simpa [StrongConvexOn] using h
  · set r := ‖w - u‖ ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hX : 0 ≤ f w - f u := sub_nonneg.2 (hmin w)
    -- key inequality: for every `t ∈ (0, 1]`, `(1 - t) * (lam / 2) * r ≤ f w - f u`
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → (1 - t) * (lam / 2 * r) ≤ f w - f u := by
      intro t ht0 ht1
      have h := hf.2 (Set.mem_univ w) (Set.mem_univ u) ht0.le (sub_nonneg.2 ht1)
        (by ring : t + (1 - t) = 1)
      have hu := hmin (t • w + (1 - t) • u)
      simp only [smul_eq_mul] at h
      have : t * ((1 - t) * (lam / 2 * r)) ≤ t * (f w - f u) := by
        rw [hr]; nlinarith
      exact le_of_mul_le_mul_left this ht0
    by_contra hcon'
    have hcon := lt_of_not_ge hcon'
    have hY : 0 < lam / 2 * r := lt_of_le_of_lt hX hcon
    set Y := lam / 2 * r
    set X := f w - f u
    have ht0 : 0 < (Y - X) / (2 * Y) := div_pos (by linarith) (by linarith)
    have ht1 : (Y - X) / (2 * Y) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have := key _ ht0 ht1
    have e : (1 - (Y - X) / (2 * Y)) * Y = (X + Y) / 2 := by
      field_simp; ring
    rw [e] at this
    linarith
