-- Prove2me | solution 1 for QualityEncroach.FixedCost.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:14:50.183196+00:00
-- url     : https://prove2.me/submissions/82e35a5c-9df3-4264-bba4-f610996a86bb

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

open Filter Topology

namespace QE3L2

lemma hasDerivAt_cubic (A B C E x : ℝ) :
    HasDerivAt (fun s => A * s ^ 3 + B * s ^ 2 + C * s + E) (3 * A * x ^ 2 + 2 * B * x + C) x := by
  have h3 := (hasDerivAt_pow 3 x).const_mul A
  have h2 := (hasDerivAt_pow 2 x).const_mul B
  have h1 := (hasDerivAt_id' x).const_mul C
  have := ((h3.add h2).add h1).add_const E
  refine this.congr_deriv ?_
  push_cast
  ring

/-- The numerator of the derivative along the constant-cost curve `s * u = v`. -/
def Nf (c v s : ℝ) : ℝ :=
  c ^ 2 * s ^ 2 * (64 * s ^ 2 - 80 * s + 5) + 24 * c * v * s ^ 2 - v ^ 2 * (20 * s ^ 2 - 16 * s + 5)

/-- Revenue along the constant-cost curve, as a single fraction. -/
noncomputable def Rf (c v s : ℝ) : ℝ :=
  (8 * c ^ 2 * s ^ 3 + (4 * v ^ 2 - 8 * c * v - c ^ 2) * s ^ 2 + 2 * c * v * s + (-v ^ 2)) /
    (32 * v * s ^ 2 + (-20 * v) * s + 0)

lemma hasDerivAt_Rf (c v s : ℝ) (hv : 0 < v) (hs : 1 < s) :
    HasDerivAt (Rf c v) (4 * v * Nf c v s / (32 * v * s ^ 2 + (-20 * v) * s + 0) ^ 2) s := by
  have hP := hasDerivAt_cubic (8 * c ^ 2) (4 * v ^ 2 - 8 * c * v - c ^ 2) (2 * c * v) (-v ^ 2) s
  have hD' : HasDerivAt (fun s => 32 * v * s ^ 2 + (-20 * v) * s + 0)
      (3 * 0 * s ^ 2 + 2 * (32 * v) * s + (-20 * v)) s := by
    have := (((hasDerivAt_pow 2 s).const_mul (32 * v)).add
      ((hasDerivAt_id' s).const_mul (-20 * v))).add_const 0
    refine this.congr_deriv ?_
    push_cast
    ring
  have hne : 32 * v * s ^ 2 + (-20 * v) * s + 0 ≠ 0 := by
    have : 0 < 32 * v * s ^ 2 + (-20 * v) * s + 0 := by
      have : 32 * v * s ^ 2 + (-20 * v) * s + 0 = 4 * v * s * (8 * s - 5) := by ring
      rw [this]; apply mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
    exact this.ne'
  have := hP.div hD' hne
  refine this.congr_deriv ?_
  unfold Nf
  ring

lemma Nf_neg (c v t : ℝ) (hc : 0 ≤ c) (hv : 0 < v) (ht : 1 < t)
    (h : 8 * t ^ 3 * c ^ 2 ≤ v ^ 2) : Nf c v t < 0 := by
  unfold Nf
  have ht0 : 0 < t := by linarith
  have hA : 24 * c * v * t ^ 2 ≤ 12 * (17 / 6 * c ^ 2 * t ^ 3 + 6 / 17 * v ^ 2 * t) := by
    nlinarith [mul_nonneg ht0.le (sq_nonneg (17 * c * t - 6 * v))]
  have hq : 0 ≤ 64 * t ^ 2 - 46 * t + 5 := by nlinarith
  have hB : 8 * t ^ 3 * c ^ 2 * (64 * t ^ 2 - 46 * t + 5) ≤ v ^ 2 * (64 * t ^ 2 - 46 * t + 5) :=
    mul_le_mul_of_nonneg_right h hq
  have hA' := mul_le_mul_of_nonneg_left hA (show (0:ℝ) ≤ 8 * t by linarith)
  have hpoly : -160 * t ^ 3 + (64 + 576 / 17 + 128) * t ^ 2 - 86 * t + 5 < 0 := by
    nlinarith [sq_nonneg (t - 1)]
  have hv2 : 0 < v ^ 2 := by positivity
  have key : 8 * t * (c ^ 2 * t ^ 2 * (64 * t ^ 2 - 80 * t + 5) + 24 * c * v * t ^ 2 -
      v ^ 2 * (20 * t ^ 2 - 16 * t + 5)) < 0 := by
    have : v ^ 2 * (-160 * t ^ 3 + (64 + 576 / 17 + 128) * t ^ 2 - 86 * t + 5) < 0 :=
      mul_neg_of_pos_of_neg hv2 hpoly
    nlinarith
  by_contra hcon
  push Not at hcon
  have : 0 ≤ 8 * t * (c ^ 2 * t ^ 2 * (64 * t ^ 2 - 80 * t + 5) + 24 * c * v * t ^ 2 -
      v ^ 2 * (20 * t ^ 2 - 16 * t + 5)) := mul_nonneg (by linarith) hcon
  linarith

lemma Nf_pos (c v t s : ℝ) (hv : 0 < v) (ht : 1 < t) (hts : t < s)
    (h0 : Nf c v t = 0) (h : v ^ 2 < 8 * t ^ 3 * c ^ 2) : 0 < Nf c v s := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by linarith
  have hid : Nf c v s * t ^ 2 - Nf c v t * s ^ 2 =
      (s - t) * (c ^ 2 * (64 * (s + t) - 80) * s ^ 2 * t ^ 2 + v ^ 2 * (5 * (s + t) - 16 * s * t)) := by
    unfold Nf; ring
  rw [h0] at hid
  have hpos1 : 0 < (64 * (s + t) - 80) * s ^ 2 * t ^ 2 := by
    apply mul_pos (mul_pos (by linarith) (by positivity)) (by positivity)
  have hm := mul_lt_mul_of_pos_right h hpos1
  have hQ : 0 ≤ (s - t) * (8 * s ^ 2 + (16 * t - 10) * s - 5 * t) := by
    apply mul_nonneg (by linarith); nlinarith
  have hbr : 0 < c ^ 2 * (64 * (s + t) - 80) * s ^ 2 * t ^ 2 + v ^ 2 * (5 * (s + t) - 16 * s * t) := by
    have e : 8 * t ^ 3 * (c ^ 2 * (64 * (s + t) - 80) * s ^ 2 * t ^ 2 +
        v ^ 2 * (5 * (s + t) - 16 * s * t)) =
        8 * t ^ 3 * c ^ 2 * ((64 * (s + t) - 80) * s ^ 2 * t ^ 2) +
        8 * t ^ 3 * v ^ 2 * (5 * (s + t) - 16 * s * t) := by ring
    have e2 : v ^ 2 * ((64 * (s + t) - 80) * s ^ 2 * t ^ 2) +
        8 * t ^ 3 * v ^ 2 * (5 * (s + t) - 16 * s * t) =
        8 * t ^ 2 * v ^ 2 * ((s - t) * (8 * s ^ 2 + (16 * t - 10) * s - 5 * t)) := by ring
    have h3 : 0 ≤ 8 * t ^ 2 * v ^ 2 * ((s - t) * (8 * s ^ 2 + (16 * t - 10) * s - 5 * t)) :=
      mul_nonneg (by positivity) hQ
    have h4 : 0 < 8 * t ^ 3 * (c ^ 2 * (64 * (s + t) - 80) * s ^ 2 * t ^ 2 +
        v ^ 2 * (5 * (s + t) - 16 * s * t)) := by linarith
    exact pos_of_mul_pos_right h4 (by positivity)
  have : 0 < Nf c v s * t ^ 2 := by
    have := mul_pos (show 0 < s - t by linarith) hbr
    linarith
  exact pos_of_mul_pos_left this (by positivity)

end QE3L2

open QE3L2 in
theorem solution (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht : 1 ≤ t) (hu : (8 * t - 3) * c < (6 * t - 3) * u)
    (hopt : ∀ t' u' : ℝ, 1 ≤ t' →
      (8 * t' - 3) * c < (6 * t' - 3) * u' →
      QualityEncroach.FixedCost.PiLo k c t' u' ≤ QualityEncroach.FixedCost.PiLo k c t u) :
    t = 1 := by
  by_contra hne
  have ht1 : 1 < t := lt_of_le_of_ne ht (Ne.symm hne)
  have ht0 : 0 < t := by linarith
  have hupos : 0 < u := by
    have : 0 ≤ (8 * t - 3) * c := mul_nonneg (by linarith) hc
    by_contra hh; push Not at hh
    nlinarith
  set v := t * u with hv
  have hvpos : 0 < v := mul_pos ht0 hupos
  -- along `s ↦ (s, v/s)`, the cost is constant and `PiLo = Rf - k v²`
  have hPi : ∀ s : ℝ, 1 < s →
      QualityEncroach.FixedCost.PiLo k c s (v / s) = Rf c v s - k * v ^ 2 := by
    intro s hs
    have hs0 : s ≠ 0 := by linarith
    have h85 : 8 * s - 5 ≠ 0 := by linarith
    have hv0 : v ≠ 0 := hvpos.ne'
    have hD : 32 * v * s ^ 2 + (-20 * v) * s + 0 ≠ 0 := by
      have : 32 * v * s ^ 2 + (-20 * v) * s + 0 = 4 * v * s * (8 * s - 5) := by ring
      rw [this]; positivity
    have hk' : QualityEncroach.FixedCost.PiLo k c s (v / s) + k * v ^ 2 = Rf c v s := by
      have hD2 : 32 * v * s ^ 2 + (-20 * v) * s + 0 = 4 * v * s * (8 * s - 5) := by ring
      unfold Rf
      rw [hD2]
      unfold QualityEncroach.FixedCost.PiLo
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_add_div _ _ (by positivity) (by positivity),
        div_sub' (by positivity), div_add' _ _ _ (by positivity),
        div_eq_div_iff (by positivity) (by positivity)]
      field_simp
      ring
    linarith
  have hvt : v / t = u := by rw [hv]; field_simp
  -- local maximality of `Rf c v` at `t`
  have hcont : ContinuousAt (fun s : ℝ => (6 * s - 3) * (v / s) - (8 * s - 3) * c) t := by
    apply ContinuousAt.sub _ (by fun_prop)
    apply ContinuousAt.mul (by fun_prop)
    exact ContinuousAt.div (by fun_prop) (by fun_prop) ht0.ne'
  have hfeas0 : 0 < (6 * t - 3) * (v / t) - (8 * t - 3) * c := by rw [hvt]; linarith
  have hev1 : ∀ᶠ s in 𝓝 t, 0 < (6 * s - 3) * (v / s) - (8 * s - 3) * c :=
    hcont.eventually (Ioi_mem_nhds hfeas0)
  have hev2 : ∀ᶠ s in 𝓝 t, 1 < s := Ioi_mem_nhds ht1
  have hloc : IsLocalMax (Rf c v) t := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    have := hopt s (v / s) hs2.le (by linarith)
    rw [hPi s hs2, ← hvt, hPi t ht1] at this
    linarith
  have hder := hasDerivAt_Rf c v t hvpos ht1
  have hz := hloc.hasDerivAt_eq_zero hder
  have hD : 32 * v * t ^ 2 + (-20 * v) * t + 0 ≠ 0 := by
    have : 32 * v * t ^ 2 + (-20 * v) * t + 0 = 4 * v * t * (8 * t - 5) := by ring
    rw [this]; apply mul_ne_zero (mul_ne_zero (by positivity) ht0.ne') (by linarith)
  have hN0 : Nf c v t = 0 := by
    rw [div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · have : 4 * v ≠ 0 := by positivity
      exact (mul_eq_zero.mp hz).resolve_left this
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz) hD
  have hbig : v ^ 2 < 8 * t ^ 3 * c ^ 2 := by
    by_contra hh; push Not at hh
    have := Nf_neg c v t hc hvpos ht1 hh
    linarith
  -- `Rf c v` is strictly increasing on `[t, ∞)`
  have hmono : StrictMonoOn (Rf c v) (Set.Ici t) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici t)
    · intro x hx
      exact (hasDerivAt_Rf c v x hvpos (lt_of_lt_of_le ht1 hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : t < x := hx
      rw [(hasDerivAt_Rf c v x hvpos (by linarith)).deriv]
      have hNx := Nf_pos c v t x hvpos ht1 hx' hN0 hbig
      have hDx : 32 * v * x ^ 2 + (-20 * v) * x + 0 ≠ 0 := by
        have : 32 * v * x ^ 2 + (-20 * v) * x + 0 = 4 * v * x * (8 * x - 5) := by ring
        rw [this]; apply mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) (by linarith)
      apply div_pos (by positivity) (by positivity)
  have hev3 : ∀ᶠ s in 𝓝[>] t, Rf c v s ≤ Rf c v t := hloc.filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs1, hs2⟩ := (hev3.and self_mem_nhdsWithin).exists
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hs2)) hs2
  linarith
