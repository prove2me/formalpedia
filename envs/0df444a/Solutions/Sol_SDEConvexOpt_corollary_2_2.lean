-- Prove2me | solution 1 for SDEConvexOpt.corollary_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:14:09.364314+00:00
-- url     : https://prove2.me/submissions/87ab7369-1064-40eb-9949-f3714ef2e218

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SDEConvexOpt_argminSet

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace Aux_SDEConvexOpt_c22

theorem descent {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hdiff : Differentiable ℝ f)
    (hLip : ∀ a b, ‖gradient f a - gradient f b‖ ≤ L * ‖a - b‖)
    (x v : EuclideanSpace ℝ (Fin d)) :
    f (x + v) ≤ f x + inner ℝ (gradient f x) v + L / 2 * ‖v‖ ^ 2 := by
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • v))
      (inner ℝ (gradient f (x + t • v)) v) t := by
    intro t
    have hγ : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id' t).smul_const v).const_add x
    have hg : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (gradient f (x + t • v))) (x + t • v) :=
      hasGradientAt_iff_hasFDerivAt.mp ((hdiff _).hasGradientAt)
    have := hg.comp_hasDerivAt t hγ
    exact this
  set c := inner ℝ (gradient f x) v with hc
  have hψ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • v) - t * c - L / 2 * (t * t) * ‖v‖ ^ 2)
      (inner ℝ (gradient f (x + t • v)) v - c - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := (hφ t).sub ((hasDerivAt_id' t).mul_const c)
    have h2 := (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
    exact (h1.sub h2).congr_deriv (by ring)
  have hanti : AntitoneOn (fun t : ℝ => f (x + t • v) - t * c - L / 2 * (t * t) * ‖v‖ ^ 2)
      (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => (hψ t).hasDerivWithinAt)
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := ht
    have h1 : inner ℝ (gradient f (x + t • v)) v - c
        = inner ℝ (gradient f (x + t • v) - gradient f x) v := by
      rw [hc, inner_sub_left]
    have h2 := real_inner_le_norm (gradient f (x + t • v) - gradient f x) v
    have h3 := hLip (x + t • v) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h3
    have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg v)
    rw [h1]
    nlinarith
  have := hanti (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp only [zero_smul, add_zero, one_smul, zero_mul, sub_zero, mul_zero, one_mul, mul_one] at this
  linarith

end Aux_SDEConvexOpt_c22

open EthierKurtz SDEConvexOpt in
theorem solution {d : ℕ} (f : SDEState d → ℝ) (L : ℝ≥0) (hf : ContDiff ℝ 1 f)
    (hL : LipschitzWith L (gradient f)) (hS : (argminSet f).Nonempty) (x : SDEState d) :
    ‖gradient f x‖ ^ 2 ≤ 2 * (L : ℝ) * (f x - ⨅ y, f y) := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hLip : ∀ a b, ‖gradient f a - gradient f b‖ ≤ (L : ℝ) * ‖a - b‖ :=
    fun a b => hL.norm_sub_le a b
  obtain ⟨xs, hxs⟩ := hS
  have hxs' : ∀ y, f xs ≤ f y := hxs
  have hbdd : BddBelow (Set.range f) := ⟨f xs, by rintro _ ⟨y, rfl⟩; exact hxs' y⟩
  have hdesc : ∀ t : ℝ, 0 ≤ t →
      f (x - t • (gradient f x)) ≤ f x - t * ‖(gradient f x)‖ ^ 2 + (L : ℝ) / 2 * (t ^ 2 * ‖(gradient f x)‖ ^ 2) := by
    intro t ht
    have h := Aux_SDEConvexOpt_c22.descent f L L.2 hdiff hLip x (-(t • (gradient f x)))
    rw [← sub_eq_add_neg, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    linarith
  have hL0 : (0 : ℝ) ≤ L := L.2
  rcases hL0.eq_or_lt with hL0 | hLpos
  · rw [← hL0, mul_zero, zero_mul]
    by_contra hcon
    push_neg at hcon
    have h := hdesc ((f x - f xs + 1) / ‖(gradient f x)‖ ^ 2) (div_nonneg (by linarith [hxs' x]) (sq_nonneg _))
    rw [← hL0, zero_div, zero_mul, add_zero, div_mul_cancel₀ _ hcon.ne'] at h
    have := hxs' (x - ((f x - f xs + 1) / ‖(gradient f x)‖ ^ 2) • (gradient f x))
    linarith
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / (L : ℝ) := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hLs : (L : ℝ) * s = 1 := by rw [hs, mul_one_div, div_self hLpos.ne']
    have h := hdesc s hs0
    have hinf : (⨅ y, f y) ≤ f (x - s • (gradient f x)) := ciInf_le hbdd _
    have e1 : (L : ℝ) * s * ‖(gradient f x)‖ ^ 2 = ‖(gradient f x)‖ ^ 2 := by rw [hLs, one_mul]
    have e2 : (L : ℝ) * (L : ℝ) * (s * s) * ‖(gradient f x)‖ ^ 2 = ‖(gradient f x)‖ ^ 2 := by
      rw [show (L : ℝ) * (L : ℝ) * (s * s) * ‖(gradient f x)‖ ^ 2 = ((L : ℝ) * s) * ((L : ℝ) * s) * ‖(gradient f x)‖ ^ 2 by ring,
        hLs]
      ring
    nlinarith [mul_le_mul_of_nonneg_left (le_trans hinf h) (by positivity : (0:ℝ) ≤ 2 * (L : ℝ))]
