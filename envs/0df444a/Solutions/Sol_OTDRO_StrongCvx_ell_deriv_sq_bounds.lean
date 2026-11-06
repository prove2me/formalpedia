-- Prove2me | solution 1 for OTDRO.StrongCvx.ell_deriv_sq_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:28:17.453878+00:00
-- url     : https://prove2.me/submissions/c494a591-82ba-46f3-a1b2-74b358cb9c7c

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Assumptions

open MeasureTheory

namespace OTDROL6

variable {d : ℕ}

lemma deriv_lip (ℓ : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ ℓ) (hd : Differentiable ℝ ℓ)
    (hdd : Differentiable ℝ (deriv ℓ)) (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (u : ℝ) :
    |deriv ℓ u| ≤ |deriv ℓ 0| + M * |u| := by
  have hmono : Monotone (deriv ℓ) := by
    have := hc.monotoneOn_deriv (fun x _ => hd x)
    intro a b hab; exact this (Set.mem_univ a) (Set.mem_univ b) hab
  have hnn : ∀ x, 0 ≤ deriv (deriv ℓ) x := fun x => hmono.deriv_nonneg
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (deriv ℓ) x‖ ≤ M := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hM x
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdd x) hb convex_univ
    (Set.mem_univ 0) (Set.mem_univ u)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (deriv ℓ u) (deriv ℓ 0)
  linarith

lemma integrable_sq_norm {P0 : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P0]
    (h4 : Integrable (fun x => ‖x‖ ^ 4) P0) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2) P0 := by
  refine Integrable.mono' (h4.add (integrable_const 1)) (by fun_prop)
    (Filter.Eventually.of_forall ?_)
  intro x
  simp only [norm_pow, Real.norm_eq_abs, abs_norm, Pi.add_apply]
  rcases le_total ‖x‖ 1 with h | h
  · have : ‖x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h
    have : 0 ≤ ‖x‖ ^ 4 := by positivity
    linarith
  · have : ‖x‖ ^ 2 ≤ ‖x‖ ^ 4 := pow_le_pow_right₀ h (by norm_num)
    linarith

end OTDROL6

open OTDROL6 in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB4 : OTDRO.StrongCvx.Assumption4 B)
    (hBne : B.Nonempty) (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) :
    ∃ Llow Lbar : ℝ, OTDRO.StrongCvx.DerivSqBounds P0 ℓ B Llow Lbar := by
  set g : ℝ → ℝ := deriv ℓ with hg
  have gcont : Continuous g := h3.deriv_differentiable.continuous
  have hlip := deriv_lip ℓ h2.convex h3.differentiable h3.deriv_differentiable M h3.second_deriv_le
  obtain ⟨R, hR⟩ := hB4.compact.isBounded.exists_norm_le
  set R' := max R 0
  have hR' : ∀ β ∈ B, ‖β‖ ≤ R' := fun β hβ => (hR β hβ).trans (le_max_left _ _)
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hM0 : 0 ≤ M := h3.M_pos.le
  set c0 := |g 0|
  -- domination
  set bound : EuclideanSpace ℝ (Fin d) → ℝ := fun x => 2 * c0 ^ 2 + 2 * (M * R') ^ 2 * ‖x‖ ^ 2
  have hbint : Integrable bound P0 :=
    (integrable_const _).add ((integrable_sq_norm h2.moment4).const_mul _)
  have hdom : ∀ β : EuclideanSpace ℝ (Fin d), ‖β‖ ≤ R' → ∀ x,
      ‖(g (inner ℝ β x)) ^ 2‖ ≤ bound x := by
    intro β hβ x
    have h1 := hlip (inner ℝ β x)
    have h4 : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := abs_real_inner_le_norm β x
    have h5 : M * |inner ℝ β x| ≤ M * R' * ‖x‖ := by
      have := mul_le_mul_of_nonneg_right hβ (norm_nonneg x)
      have := mul_le_mul_of_nonneg_left (h4.trans this) hM0
      linarith
    have h6 : |g (inner ℝ β x)| ≤ c0 + M * R' * ‖x‖ := by linarith
    have h7 : 0 ≤ |g (inner ℝ β x)| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_pow, show bound x = 2 * c0 ^ 2 + 2 * (M * R') ^ 2 * ‖x‖ ^ 2 from rfl]
    have : |g (inner ℝ β x)| ^ 2 ≤ (c0 + M * R' * ‖x‖) ^ 2 := pow_le_pow_left₀ h7 h6 2
    nlinarith [sq_nonneg (c0 - M * R' * ‖x‖)]
  have hmeas : ∀ β : EuclideanSpace ℝ (Fin d),
      AEStronglyMeasurable (fun x => (g (inner ℝ β x)) ^ 2) P0 := by
    intro β
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  have hint : ∀ β ∈ B, Integrable (fun x => (g (inner ℝ β x)) ^ 2) P0 := by
    intro β hβ
    exact Integrable.mono' hbint (hmeas β) (Filter.Eventually.of_forall (hdom β (hR' β hβ)))
  set I : EuclideanSpace ℝ (Fin d) → ℝ := fun β => ∫ x, (g (inner ℝ β x)) ^ 2 ∂P0
  have hIcont : ContinuousOn I B := by
    refine continuousOn_of_dominated (fun β _ => hmeas β)
      (fun β hβ => Filter.Eventually.of_forall (hdom β (hR' β hβ))) hbint
      (Filter.Eventually.of_forall fun x => ?_)
    exact (Continuous.continuousOn (by fun_prop))
  have hIpos : ∀ β ∈ B, 0 < I β := by
    intro β hβ
    have hnn : 0 ≤ᵐ[P0] (fun x => (g (inner ℝ β x)) ^ 2) :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    show 0 < ∫ x, (g (inner ℝ β x)) ^ 2 ∂P0
    rw [integral_pos_iff_support_of_nonneg_ae hnn (hint β hβ)]
    have hnz := h3.nonzero_deriv β hβ
    rw [Filter.Eventually, mem_ae_iff] at hnz
    refine pos_iff_ne_zero.2 ?_
    intro h0
    apply hnz
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero]
    exact hx
  obtain ⟨βmin, hβmin, hmin⟩ := hB4.compact.exists_isMinOn hBne hIcont
  obtain ⟨βmax, hβmax, hmax⟩ := hB4.compact.exists_isMaxOn hBne hIcont
  refine ⟨I βmin, I βmax, hIpos βmin hβmin, hIpos βmax hβmax, fun β hβ => ⟨hint β hβ, ?_, ?_⟩⟩
  · exact hmin hβ
  · exact hmax hβ
