-- Prove2me | solution 1 for ParamMCF.MCA.spline_abs_ge
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:47:34.38898+00:00
-- url     : https://prove2.me/submissions/7298a94b-9b71-42f9-98e8-38c6f3317e3b

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- A continuous function that is nonpositive on negatives is nonpositive at zero. -/
lemma pmcf_nonpos_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, s < 0 → φ s ≤ 0) :
    φ 0 ≤ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Iio 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A continuous function that is nonnegative on positives is nonnegative at zero. -/
lemma pmcf_nonneg_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, 0 < s → 0 ≤ φ s) :
    0 ≤ φ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- Under the shape condition, `g'' = 0` on `(-∞, 0]`. -/
lemma pmcf_f2_zero_nonpos (g : ℝ → ℝ)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0)) :
    ∀ x, x ≤ 0 → deriv (deriv g) x = 0 := by
  have hc : Continuous (deriv (deriv g)) := hg3.2.continuous
  have h0 : deriv (deriv g) 0 = 0 := le_antisymm
    (pmcf_nonpos_at_zero _ hc.continuousAt hshape.2.2.2) (hshape.2.1 0 le_rfl)
  intro x hx
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, h0]
  · apply le_antisymm (hshape.2.2.2 x h)
    have ht : Filter.Tendsto (deriv (deriv g)) (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv (deriv g) 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hle : deriv (deriv g) 0 ≤ deriv (deriv g) x := by
      apply le_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT h] with y hy
      exact hshape.2.2.1 (Set.mem_Iio.2 h) (Set.mem_Iio.2 hy.2) hy.1.le
    linarith [hshape.2.1 0 le_rfl]

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

/-- Every point of `[x_0, x_K]` lies in some closed mesh interval. -/
lemma pmcf_exists_interval (K : ℕ) (xs : Fin (K + 1) → ℝ) (hK : 0 < K) (x : ℝ)
    (hl : x ≤ xs (Fin.last K)) (h0 : xs 0 ≤ x) :
    ∃ i : Fin K, x ∈ Set.Icc (xs i.castSucc) (xs i.succ) := by
  have hmem : (⟨K - 1, Nat.sub_lt hK one_pos⟩ : Fin K) ∈
      Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
    have : (⟨K - 1, Nat.sub_lt hK one_pos⟩ : Fin K).succ = Fin.last K := by
      ext; simp; omega
    simp [this, hl]
  have hne : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := ⟨_, hmem⟩
  set i := (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).min' hne with hi
  have himem : i ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := Finset.min'_mem _ _
  refine ⟨i, ?_, (Finset.mem_filter.1 himem).2⟩
  rcases Nat.eq_zero_or_pos i.val with h | h
  · have : i.castSucc = 0 := by ext; simp [h]
    rw [this]; exact h0
  · set j : Fin K := ⟨i.val - 1, by omega⟩ with hj
    have hjs : j.succ = i.castSucc := by ext; simp [hj]; omega
    by_contra hcon
    push_neg at hcon
    have hjmem : j ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hjs]; exact hcon.le
    have := Finset.min'_le _ _ hjmem
    rw [← hi, Fin.le_def] at this
    simp [hj] at this
    omega

/-- If `0` is a mesh point, no mesh interval straddles `0`. -/
lemma pmcf_side (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (hzero : ∃ j, xs j = 0)
    (i : Fin K) : xs i.succ ≤ 0 ∨ 0 ≤ xs i.castSucc := by
  obtain ⟨j, hj⟩ := hzero
  by_contra hcon
  push_neg at hcon
  have h1 : i.castSucc < j := hxs.lt_iff_lt.1 (by rw [hj]; exact hcon.2)
  have h2 : j < i.succ := hxs.lt_iff_lt.1 (by rw [hj]; exact hcon.1)
  rw [Fin.lt_def] at h1 h2
  simp at h1 h2
  omega

/-- A marginal cost vanishes at zero. -/
lemma pmcf_g_zero (g : ℝ → ℝ) (hg : IsMarginalCost g) : g 0 = 0 :=
  le_antisymm (pmcf_nonpos_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.2)
    (pmcf_nonneg_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.1)

lemma pmcf_g_nonneg (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, pmcf_g_zero g hg]
  · exact hg.2.2.1 x h

lemma pmcf_g_nonpos (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : x ≤ 0) : g x ≤ 0 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, pmcf_g_zero g hg]
  · exact hg.2.2.2 x h

theorem spline_abs_ge_sol (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (X : ℝ) (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (hfirst : xs 0 = -X) (hlast : xs (Fin.last K) = X) (hzero : ∃ j, xs j = 0) :
    ∀ x ∈ Set.Icc (-X) X, |g x| ≤ |linSpline K xs g x| := by
  intro x hx
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hl0 : (Fin.last 0) = (0 : Fin 1) := rfl
    rw [hl0] at hlast
    have hxe : x = xs 0 := by linarith [hx.1, hx.2]
    have : linSpline 0 xs g x = g (xs 0) := by
      unfold linSpline; rw [dif_neg (lt_irrefl 0)]
    rw [this, hxe]
  obtain ⟨i, hi⟩ := pmcf_exists_interval K xs hK x (hlast ▸ hx.2) (hfirst ▸ hx.1)
  rw [pmcf_linSpline_eq_piece K xs hxs g i x hi]
  unfold splinePiece
  have hlt : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
  have hz := pmcf_f2_zero_nonpos g hg3 hshape
  rcases pmcf_side K xs hxs hzero i with hs | hs
  · -- interval in `(-∞, 0]`: chord below `g`, `g ≤ 0`
    have hc := pmcf_chord_lower g hg.2.1 hg3.1 _ _ 0 hlt
      (fun ξ hξ => (hz ξ (hξ.2.trans hs)).le) x hi
    have hgx := pmcf_g_nonpos g hg x (hi.2.trans hs)
    rw [abs_of_nonpos hgx, abs_of_nonpos (by nlinarith)]
    nlinarith
  · -- interval in `[0, ∞)`: chord above `g`, `g ≥ 0`
    have hdn : deriv (fun t => -g t) = fun t => -deriv g t := by
      funext t; exact deriv.neg
    have hng2 : Differentiable ℝ (deriv (fun t => -g t)) := by rw [hdn]; exact hg3.1.neg
    have hddn : deriv (deriv (fun t => -g t)) = fun t => -deriv (deriv g) t := by
      rw [hdn]; funext t; exact deriv.neg
    have hc := pmcf_chord_lower (fun t => -g t) hg.2.1.neg hng2 _ _ 0 hlt
      (fun ξ hξ => by rw [hddn]; simp only; linarith [hshape.2.1 ξ (hs.trans hξ.1)]) x hi
    have hgx := pmcf_g_nonneg g hg x (hs.trans hi.1)
    rw [abs_of_nonneg hgx, abs_of_nonneg (by nlinarith)]
    nlinarith

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (X : ℝ) (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (hfirst : xs 0 = -X) (hlast : xs (Fin.last K) = X) (hzero : ∃ j, xs j = 0) :
    ∀ x ∈ Set.Icc (-X) X, |g x| ≤ |linSpline K xs g x| :=
  spline_abs_ge_sol g hg hg3 hshape X K xs hxs hfirst hlast hzero
