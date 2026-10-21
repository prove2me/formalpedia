-- Prove2me | solution 1 for ParamMCF.MCA.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:44:40.078754+00:00
-- url     : https://prove2.me/submissions/60da3720-5e1c-4bb7-a7b1-121e6ad05596

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- One-sided chord error bound via concavity. -/
lemma pmcf_chord_lower (g : ℝ → ℝ) (hg1 : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (a b M : ℝ) (hab : a < b) (hM : ∀ ξ ∈ Set.Icc a b, deriv (deriv g) ξ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    M / 2 * ((x - a) * (x - b)) ≤
      g x - (g a + (x - a) / (b - a) * (g b - g a)) := by
  set c := (g b - g a) / (b - a) with hc
  set h : ℝ → ℝ := fun t => g t - (g a + (t - a) * c) - M / 2 * ((t - a) * (t - b)) with hh
  have hd1 : ∀ t, HasDerivAt h (deriv g t - c - M / 2 * ((t - b) + (t - a))) t := by
    intro t
    have h1 := (hg1 t).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => g a + (t - a) * c) c t := by
      exact ((((hasDerivAt_id' t).sub_const a).mul_const c).const_add (g a)).congr_deriv (by ring)
    have h3 : HasDerivAt (fun t : ℝ => (t - a) * (t - b)) ((t - b) + (t - a)) t := by
      exact (((hasDerivAt_id' t).sub_const a).fun_mul ((hasDerivAt_id' t).sub_const b)).congr_deriv (by ring)
    exact (h1.fun_sub h2).fun_sub (h3.const_mul (M / 2))
  have hd2 : ∀ t, HasDerivAt (fun t => deriv g t - c - M / 2 * ((t - b) + (t - a)))
      (deriv (deriv g) t - M) t := by
    intro t
    have h1 := (hg2 t).hasDerivAt
    have h3 : HasDerivAt (fun t : ℝ => (t - b) + (t - a)) 2 t := by
      exact (((hasDerivAt_id' t).sub_const b).fun_add ((hasDerivAt_id' t).sub_const a)).congr_deriv (by norm_num)
    exact ((h1.sub_const c).fun_sub (h3.const_mul (M / 2))).congr_deriv (by ring)
  have hconc : ConcaveOn ℝ (Set.Icc a b) h := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
      (f' := fun t => deriv g t - c - M / 2 * ((t - b) + (t - a)))
      (f'' := fun t => deriv (deriv g) t - M) ?_ ?_ ?_ ?_
    · exact fun t _ => (hd1 t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd1 t).hasDerivWithinAt
    · exact fun t _ => (hd2 t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have := hM t ⟨ht.1.le, ht.2.le⟩
      linarith
  have hmin := hconc.ge_on_segment (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le)
    (z := x) (by rw [segment_eq_Icc hab.le]; exact hx)
  have ha : h a = 0 := by simp [hh]
  have hb : h b = 0 := by
    simp only [hh, hc]
    field_simp [sub_ne_zero.2 hab.ne']
    ring
  rw [ha, hb, min_self] at hmin
  have : h x = g x - (g a + (x - a) / (b - a) * (g b - g a)) - M / 2 * ((x - a) * (x - b)) := by
    simp only [hh, hc]; ring
  linarith

/-- Two-sided chord error bound. -/
lemma pmcf_chord_abs (g : ℝ → ℝ) (hg1 : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (a b M : ℝ) (hab : a < b) (hM : ∀ ξ ∈ Set.Icc a b, |deriv (deriv g) ξ| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    |g x - (g a + (x - a) / (b - a) * (g b - g a))| ≤ (1 / 8 : ℝ) * (b - a) ^ 2 * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a (Set.left_mem_Icc.2 hab.le))
  have h1 := pmcf_chord_lower g hg1 hg2 a b M hab (fun ξ hξ => (le_abs_self _).trans (hM ξ hξ)) x hx
  have hng1 : Differentiable ℝ (fun t => -g t) := hg1.neg
  have hdn : deriv (fun t => -g t) = fun t => -deriv g t := by
    funext t; exact deriv.neg
  have hng2 : Differentiable ℝ (deriv (fun t => -g t)) := by rw [hdn]; exact hg2.neg
  have hddn : deriv (deriv (fun t => -g t)) = fun t => -deriv (deriv g) t := by
    rw [hdn]; funext t; exact deriv.neg
  have h2 := pmcf_chord_lower (fun t => -g t) hng1 hng2 a b M hab
    (fun ξ hξ => by rw [hddn]; exact (neg_le_abs _).trans (hM ξ hξ)) x hx
  have hq : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hq0 : 0 ≤ (x - a) * (b - x) := mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hq hM0]
  · nlinarith [mul_le_mul_of_nonneg_left hq hM0]

/-- On a closed mesh interval, the spline coincides with that interval's chord. -/
lemma pmcf_linSpline_eq_piece (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (g : ℝ → ℝ) (i : Fin K) (x : ℝ) (hx : x ∈ Set.Icc (xs i.castSucc) (xs i.succ)) :
    linSpline K xs g x = splinePiece K xs g i x := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  unfold linSpline
  rw [dif_pos hK]
  have hmem : i ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
    simp [hx.2]
  have hne : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := ⟨i, hmem⟩
  simp only
  rw [dif_pos hne]
  set j := (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).min' hne with hj
  have hjmem : j ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := Finset.min'_mem _ _
  have hjx : x ≤ xs j.succ := (Finset.mem_filter.1 hjmem).2
  have hji : j ≤ i := Finset.min'_le _ _ hmem
  rcases eq_or_lt_of_le hji with h | h
  · rw [h]
  · have hle : j.succ ≤ i.castSucc := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact h
    have h1 : xs j.succ ≤ xs i.castSucc := hxs.monotone hle
    have hxe : x = xs j.succ := le_antisymm hjx (h1.trans hx.1)
    have hxe' : x = xs i.castSucc := le_antisymm (hjx.trans h1) hx.1
    unfold splinePiece
    have hne1 : xs j.succ - xs j.castSucc ≠ 0 :=
      sub_ne_zero.2 (hxs (Fin.castSucc_lt_succ (i := j))).ne'
    rw [show x - xs i.castSucc = 0 by rw [hxe']; ring, zero_div, zero_mul, add_zero]
    rw [show x - xs j.castSucc = xs j.succ - xs j.castSucc by rw [hxe], div_self hne1, one_mul]
    rw [show xs i.castSucc = xs j.succ by rw [← hxe, ← hxe']]
    ring

theorem eq_18_sol (g : ℝ → ℝ)
    (hg : Differentiable ℝ g ∧ Differentiable ℝ (deriv g))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (i : Fin K) (x M : ℝ)
    (hx : x ∈ Set.Icc (xs i.castSucc) (xs i.succ))
    (hM : ∀ ξ ∈ Set.Icc (xs i.castSucc) (xs i.succ), |deriv (deriv g) ξ| ≤ M) :
    |g x - linSpline K xs g x| ≤
      (1 / 8 : ℝ) * (xs i.succ - xs i.castSucc) ^ 2 * M := by
  rw [pmcf_linSpline_eq_piece K xs hxs g i x hx]
  unfold splinePiece
  have hlt : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
  have := pmcf_chord_abs g hg.1 hg.2 _ _ M hlt hM x hx
  convert this using 3

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution (g : ℝ → ℝ)
    (hg : Differentiable ℝ g ∧ Differentiable ℝ (deriv g))
    (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (i : Fin K) (x M : ℝ)
    (hx : x ∈ Set.Icc (xs i.castSucc) (xs i.succ))
    (hM : ∀ ξ ∈ Set.Icc (xs i.castSucc) (xs i.succ), |deriv (deriv g) ξ| ≤ M) :
    |g x - linSpline K xs g x| ≤
      (1 / 8 : ℝ) * (xs i.succ - xs i.castSucc) ^ 2 * M :=
  eq_18_sol g hg K xs hxs i x M hx hM
