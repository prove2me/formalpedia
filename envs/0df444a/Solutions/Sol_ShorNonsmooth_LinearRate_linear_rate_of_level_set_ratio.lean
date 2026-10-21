-- Prove2me | solution 1 for ShorNonsmooth.LinearRate.linear_rate_of_level_set_ratio
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T23:52:33.556983+00:00
-- url     : https://prove2.me/submissions/5c43d071-3601-4268-bab4-c4fe1e5982b2

import Mathlib
import Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod
namespace ShorLinearProof
open ShorNonsmooth.AlmostDiff ShorNonsmooth.SubgradMethod
open scoped InnerProductSpace
end ShorLinearProof

namespace ShorLinearProof
open ShorNonsmooth.AlmostDiff ShorNonsmooth.SubgradMethod
open scoped InnerProductSpace

lemma minimum_le {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : MinSet f = {xs}) (y) : f xs ≤ f y := by
  have hm : xs ∈ MinSet f := by rw [hxs]; simp
  exact hm y

lemma minimum_value_unique {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xs x : EuclideanSpace ℝ (Fin n)} (hxs : MinSet f = {xs})
    (he : f x = f xs) : x = xs := by
  have hm : x ∈ MinSet f := by intro y; rw [he]; exact minimum_le hxs y
  simpa only [hxs, Set.mem_singleton_iff] using hm

lemma zero_subgradient_min {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xs x v : EuclideanSpace ℝ (Fin n)} (hxs : MinSet f = {xs})
    (hg : IsSubgradient f x v) (hv : v = 0) : x = xs := by
  have hm : x ∈ MinSet f := by
    intro y
    have hy := hg y
    rw [hv, inner_zero_left] at hy
    linarith
  simpa only [hxs, Set.mem_singleton_iff] using hm

lemma level_angle {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {xs : EuclideanSpace ℝ (Fin n)}
    (hxs : MinSet f = {xs}) {σ R : ℝ} (hσ : 0 < σ)
    (hY : ∀ x ∈ Metric.closedBall xs R, ∀ z ∈ Metric.closedBall xs R,
      f x = f z → f x ≠ f xs → ‖x - xs‖ ≤ σ * ‖z - xs‖)
    {x v : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall xs R)
    (hg : IsSubgradient f x v) : ‖v‖ * ‖x - xs‖ ≤ σ * inner ℝ v (x - xs) := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases he : f x = f xs
  · have hxe := minimum_value_unique hxs he
    simp [hxe]
  have hG : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let ray : ℝ → EuclideanSpace ℝ (Fin n) := fun t => xs + (t / ‖v‖) • v
  have ray_dist (t : ℝ) (ht : 0 ≤ t) : ‖ray t - xs‖ = t := by
    dsimp [ray]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ht hG.le), div_mul_cancel₀ _ hG.ne']
  have ray_inner (t : ℝ) : inner ℝ v (ray t - x) =
      t * ‖v‖ - inner ℝ v (x - xs) := by
    have hid : ray t - x = (t / ‖v‖) • v - (x - xs) := by dsimp [ray]; abel
    rw [hid, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hr : 0 ≤ ‖x - xs‖ := norm_nonneg _
  have hend : f x ≤ f (ray ‖x - xs‖) := by
    have hs := hg (ray ‖x - xs‖)
    rw [ray_inner] at hs
    have hc := real_inner_le_norm v (x - xs)
    nlinarith
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hrc : Continuous (fun t : ℝ => f (ray t)) :=
    hcont.comp (continuous_const.add ((continuous_id.div_const _).smul continuous_const))
  obtain ⟨t, ht, hlevel⟩ := intermediate_value_Icc hr hrc.continuousOn
    (show f x ∈ Set.Icc (f (ray 0)) (f (ray ‖x - xs‖)) from
      ⟨by simpa [ray] using minimum_le hxs x, hend⟩)
  change f (ray t) = f x at hlevel
  have hmem : ray t ∈ Metric.closedBall xs R := by
    rw [Metric.mem_closedBall, dist_eq_norm, ray_dist t ht.1]
    exact ht.2.trans (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
  have hshape := hY x hx (ray t) hmem hlevel.symm he
  rw [ray_dist t ht.1] at hshape
  have hs := hg (ray t)
  rw [hlevel, sub_self, ray_inner] at hs
  have ha := mul_le_mul_of_nonneg_right hshape hG.le
  have hb := mul_le_mul_of_nonneg_left (show t * ‖v‖ ≤ inner ℝ v (x-xs) by linarith) hσ.le
  nlinarith

end ShorLinearProof

namespace ShorLinearProof
open scoped InnerProductSpace

lemma normalized_step_sq {n : ℕ} {x xs v : EuclideanSpace ℝ (Fin n)}
    {σ H : ℝ} (hσ : 0 < σ) (hH : 0 ≤ H) (hv : v ≠ 0)
    (ha : ‖v‖ * ‖x-xs‖ ≤ σ * inner ℝ v (x-xs)) :
    ‖x - (H / ‖v‖) • v - xs‖ ^ 2 ≤
      ‖x-xs‖ ^ 2 - 2 * H * ‖x-xs‖ / σ + H ^ 2 := by
  have hG : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hi : ‖x-xs‖ / σ ≤ inner ℝ v (x-xs) / ‖v‖ := by
    apply (div_le_div_iff₀ hσ hG).mpr
    nlinarith [ha]
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * H by positivity)
  have hid : x - (H / ‖v‖) • v - xs = (x-xs) - (H / ‖v‖) • v := by abel
  rw [hid, norm_sub_sq_real, inner_smul_right, real_inner_comm v (x-xs),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hH hG.le),
    div_mul_cancel₀ _ hG.ne']
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith [hm]

end ShorLinearProof

namespace ShorLinearProof

lemma sigma_pos {σ : ℝ} (hσ : Real.sqrt 2 ≤ σ) : 0 < σ :=
  lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) hσ

lemma sigma_sq {σ : ℝ} (hσ : Real.sqrt 2 ≤ σ) : 2 ≤ σ ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := sigma_pos hσ
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

lemma step_ratio_bounds {σ : ℝ} (hσ : Real.sqrt 2 ≤ σ) :
    0 ≤ Real.sqrt (σ ^ 2 - 1) / σ ∧ Real.sqrt (σ ^ 2 - 1) / σ ≤ 1 := by
  have hp := sigma_pos hσ
  have hs := sigma_sq hσ
  have ha : 0 ≤ σ ^ 2 - 1 := by linarith
  have he := Real.sq_sqrt ha
  constructor
  · exact div_nonneg (Real.sqrt_nonneg _) hp.le
  · apply (div_le_one hp).2
    nlinarith [Real.sqrt_nonneg (σ ^ 2 - 1)]

lemma schedule_bounds {σ : ℝ} {h : ℕ → ℝ} (hσ : Real.sqrt 2 ≤ σ)
    (h₁ : 0 ≤ h 1)
    (hrec : ∀ k, 1 ≤ k → h (k + 1) = h k * (Real.sqrt (σ ^ 2 - 1) / σ)) :
    ∀ k, 0 ≤ h (k + 1) ∧ h (k + 1) ≤ h 1 := by
  have hb := step_ratio_bounds hσ
  intro k
  induction k with
  | zero => exact ⟨h₁, le_rfl⟩
  | succ k ih =>
      rw [hrec (k + 1) (by omega)]
      exact ⟨mul_nonneg ih.1 hb.1,
        (mul_le_of_le_one_right ih.1 hb.2).trans ih.2⟩

/-- The full interval estimate includes an iterate at the minimum with a nonzero subgradient. -/
lemma overshoot_bound {σ H r d : ℝ} (hσ : Real.sqrt 2 ≤ σ) (hH : 0 ≤ H)
    (hr : 0 ≤ r) (hcap : r ≤ H * σ)
    (hstep : d ^ 2 ≤ r ^ 2 - 2 * H * r / σ + H ^ 2) :
    d ≤ H * Real.sqrt (σ ^ 2 - 1) := by
  have hp := sigma_pos hσ
  have hs := sigma_sq hσ
  have hc : 0 ≤ σ - 2 / σ := by
    apply sub_nonneg.2
    apply (div_le_iff₀ hp).2
    nlinarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hcap)
    (add_nonneg hr (mul_nonneg hc hH))
  have hid : (r - H * σ) * (r + (σ - 2 / σ) * H) =
      r ^ 2 - 2 * H * r / σ + H ^ 2 - (σ ^ 2 - 1) * H ^ 2 := by
    field_simp
    ring
  rw [hid] at hprod
  have ha : 0 ≤ σ ^ 2 - 1 := by linarith
  have he := Real.sq_sqrt ha
  have hn : 0 ≤ H * Real.sqrt (σ ^ 2 - 1) :=
    mul_nonneg hH (Real.sqrt_nonneg _)
  have he' : (H * Real.sqrt (σ ^ 2 - 1)) ^ 2 = (σ ^ 2 - 1) * H ^ 2 := by
    rw [mul_pow, he]
    ring
  nlinarith

end ShorLinearProof

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), p. 32, **Theorem 2.8**. Let `f` be convex on `E_n` with unique minimum point
`x*`. For a starting point `x₀` let `σ ≥ √2` and `h₁ ≥ ‖x₀ - x*‖/σ`, let
`Y = {y : ‖y - x*‖ ≤ σ h₁}`, and assume (2.20): `‖x - x*‖ ≤ σ ‖z - x*‖` for every pair
`x, z ∈ Y` with `f(x) = f(z) ≠ f(x*)`. Then the normalized subgradient iterates with stepsizes
`h_{k+1} = h_k √(σ² - 1)/σ` (`k ≥ 1`) satisfy (2.21): `‖x_k - x*‖ ≤ h_{k+1} σ` for all `k`.
The book's exception "`g_f(x_k̄) = 0`, i.e. `x_k̄ = x*`" is the stop of the method; the stopped
sequence stays at `x*`, where the bound holds trivially. -/
theorem linear_rate_of_level_set_ratio {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ShorNonsmooth.SubgradMethod.MinSet f = {xs})
    (x₀ : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (h : ℕ → ℝ)
    (hσ : Real.sqrt 2 ≤ σ) (hh₁ : ‖x₀ - xs‖ / σ ≤ h 1)
    (hY : ∀ x ∈ Metric.closedBall xs (σ * h 1), ∀ z ∈ Metric.closedBall xs (σ * h 1),
      f x = f z → f x ≠ f xs → ‖x - xs‖ ≤ σ * ‖z - xs‖)
    (hrec : ∀ k, 1 ≤ k → h (k + 1) = h k * (Real.sqrt (σ ^ 2 - 1) / σ))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) :
    ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - xs‖ ≤ h (k + 1) * σ := by
  classical
  have hs := ShorLinearProof.sigma_pos hσ
  have h₁ : 0 ≤ h 1 := (div_nonneg (norm_nonneg _) hs.le).trans hh₁
  have hb := ShorLinearProof.schedule_bounds hσ h₁ hrec
  intro k
  induction k with
  | zero =>
      simpa only [ShorNonsmooth.SubgradMethod.normalizedIter] using
        (div_le_iff₀ hs).mp hh₁
  | succ k ih =>
      let x := ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k
      have hx : x ∈ Metric.closedBall xs (σ * h 1) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact ih.trans (by nlinarith [(hb k).2])
      by_cases hz : g x = 0
      · have he : x = xs := ShorLinearProof.zero_subgradient_min hxs (hg x) hz
        have hn : 0 ≤ h (k + 1 + 1) * σ := mul_nonneg (hb (k+1)).1 hs.le
        change ‖(if g x = 0 then x else x - (h (k+1) / ‖g x‖) • g x) - xs‖ ≤ _
        rw [if_pos hz, he, sub_self, norm_zero]
        exact hn
      · have ha := ShorLinearProof.level_angle hf hxs hs hY hx (hg x)
        have hstep := ShorLinearProof.normalized_step_sq hs (hb k).1 hz ha
        have hd := ShorLinearProof.overshoot_bound hσ (hb k).1 (norm_nonneg (x-xs)) ih hstep
        have hid : h (k+1) * Real.sqrt (σ^2-1) = h (k+1+1) * σ := by
          rw [hrec (k+1) (by omega)]
          field_simp
        rw [hid] at hd
        change ‖(if g x = 0 then x else x - (h (k+1) / ‖g x‖) • g x) - xs‖ ≤ _
        rw [if_neg hz]
        exact hd


end ShorNonsmooth.LinearRate

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ShorNonsmooth.SubgradMethod.MinSet f = {xs})
    (x₀ : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (h : ℕ → ℝ)
    (hσ : Real.sqrt 2 ≤ σ) (hh₁ : ‖x₀ - xs‖ / σ ≤ h 1)
    (hY : ∀ x ∈ Metric.closedBall xs (σ * h 1), ∀ z ∈ Metric.closedBall xs (σ * h 1),
      f x = f z → f x ≠ f xs → ‖x - xs‖ ≤ σ * ‖z - xs‖)
    (hrec : ∀ k, 1 ≤ k → h (k + 1) = h k * (Real.sqrt (σ ^ 2 - 1) / σ))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) :
    ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - xs‖ ≤ h (k + 1) * σ :=
  ShorNonsmooth.LinearRate.linear_rate_of_level_set_ratio f hf xs hxs x₀ σ h hσ hh₁ hY hrec g hg
