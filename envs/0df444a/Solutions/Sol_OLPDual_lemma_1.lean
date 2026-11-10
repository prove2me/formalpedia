-- Prove2me | solution 1 for OLPDual.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:31:12.871749+00:00
-- url     : https://prove2.me/submissions/fab08c61-e61e-42ae-80fa-51be0eb373cc

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Aux_OLPDual_l1

theorem kn (x y r : ℝ) :
    ∫ v in x..y, ((if r > v then (1 : ℝ) else 0) - (if r > y then (1 : ℝ) else 0)) =
      (max (r - x) 0 - max (r - y) 0) - (y - x) * (if r > y then (1 : ℝ) else 0) := by
  have hi1 : IntervalIntegrable (fun v : ℝ => if r > v then (1 : ℝ) else 0) MeasureTheory.volume x y := by
    apply Antitone.intervalIntegrable
    intro v w hvw
    show (if r > w then (1 : ℝ) else 0) ≤ (if r > v then (1 : ℝ) else 0)
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso; exact h2 (lt_of_le_of_lt hvw h1)
    · norm_num
    · exact le_rfl
  have hderiv : ∀ v : ℝ, HasDerivWithinAt (fun w : ℝ => min w r)
      (if r > v then (1 : ℝ) else 0) (Set.Ioi v) v := by
    intro v
    by_cases hv : r > v
    · rw [if_pos hv]
      apply HasDerivAt.hasDerivWithinAt
      apply (hasDerivAt_id v).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hv] with w hw
      exact min_eq_left hw.le
    · rw [if_neg hv]
      push_neg at hv
      apply (hasDerivWithinAt_const v (Set.Ioi v) r).congr
      · intro w hw
        exact min_eq_right (le_trans hv (le_of_lt hw))
      · exact min_eq_right hv
  have hftc : ∫ v in x..y, (if r > v then (1 : ℝ) else 0) = min y r - min x r :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (continuous_id.min continuous_const).continuousOn (fun v _ => hderiv v) hi1
  have hm : ∀ t, min t r = r - max (r - t) 0 := by
    intro t
    rcases le_total t r with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  rw [intervalIntegral.integral_sub hi1 intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, hftc, hm, hm]
  ring

end Aux_OLPDual_l1

open OLPDual in
theorem solution (Θ : Model) {m : ℕ} (d : E m) (law : Measure (E m × ℝ))
    [IsProbabilityMeasure law] (hA1 : Assumption1 Θ d law) (p pstar : E m) :
    f d law p - f d law pstar =
      ⟪gradf d law pstar, p - pstar⟫ + ∫ u, knightTerm u.1 u.2 p pstar ∂law := by
  have hb := hA1.bounded
  have hmx : ∀ q : E m, Measurable (fun u : E m × ℝ => ⟪u.1, q⟫) :=
    fun q => (continuous_fst.inner continuous_const).measurable
  have hmr : Measurable (fun u : E m × ℝ => u.2) := measurable_snd
  have hset : MeasurableSet {u : E m × ℝ | ⟪u.1, pstar⟫ < u.2} := measurableSet_lt (hmx pstar) hmr
  have hind : Measurable (fun u : E m × ℝ => if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hxb : ∀ q : E m, ∀ᵐ u ∂law, |⟪u.1, q⟫| ≤ Θ.abar * ‖q‖ := by
    intro q
    filter_upwards [hb] with u hu
    exact le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _))
  have hmaxI : ∀ q : E m, Integrable (fun u : E m × ℝ => max (u.2 - ⟪u.1, q⟫) 0) law := by
    intro q
    refine Integrable.of_bound ((hmr.sub (hmx q)).max measurable_const).aestronglyMeasurable
      (Θ.rbar + Θ.abar * ‖q‖) ?_
    filter_upwards [hb, hxb q] with u hu hxq
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have := le_abs_self u.2
      have := neg_abs_le ⟪u.1, q⟫
      linarith [hu.1]
    · have := Θ.rbar_pos
      have := mul_nonneg Θ.abar_pos.le (norm_nonneg q)
      linarith
  have hI3 : Integrable (fun u : E m × ℝ =>
      (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) * (⟪u.1, p⟫ - ⟪u.1, pstar⟫)) law := by
    refine Integrable.of_bound (hind.mul ((hmx p).sub (hmx pstar))).aestronglyMeasurable
      (Θ.abar * ‖p‖ + Θ.abar * ‖pstar‖) ?_
    filter_upwards [hxb p, hxb pstar] with u h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    have hi : |(if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have hd : |⟪u.1, p⟫ - ⟪u.1, pstar⟫| ≤ Θ.abar * ‖p‖ + Θ.abar * ‖pstar‖ :=
      le_trans (abs_sub _ _) (add_le_add h1 h2)
    calc |(if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0)| * |⟪u.1, p⟫ - ⟪u.1, pstar⟫|
        ≤ 1 * (Θ.abar * ‖p‖ + Θ.abar * ‖pstar‖) :=
          mul_le_mul hi hd (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hphiI : Integrable (phi d pstar) law := by
    have hmeas : Measurable (phi d pstar) := by
      unfold phi
      exact measurable_const.sub (Measurable.ite hset measurable_fst measurable_const)
    refine Integrable.of_bound hmeas.aestronglyMeasurable (‖d‖ + Θ.abar) ?_
    filter_upwards [hb] with u hu
    unfold phi
    refine le_trans (norm_sub_le _ _) (add_le_add le_rfl ?_)
    split_ifs
    · exact hu.2
    · rw [norm_zero]; exact Θ.abar_pos.le
  have hinner : ⟪gradf d law pstar, p - pstar⟫ = ∫ u, ⟪phi d pstar u, p - pstar⟫ ∂law := by
    unfold gradf
    rw [real_inner_comm, ← integral_inner (𝕜 := ℝ) hphiI]
    congr 1
    funext u
    exact real_inner_comm _ _
  have hpt : ∀ u : E m × ℝ, ⟪phi d pstar u, p - pstar⟫ = ⟪d, p - pstar⟫ -
      (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) * (⟪u.1, p⟫ - ⟪u.1, pstar⟫) := by
    intro u
    unfold phi
    rw [inner_sub_left]
    split_ifs
    · simp only [inner_sub_right, one_mul]
    · rw [inner_zero_left, zero_mul]
  have hK : ∀ u : E m × ℝ, knightTerm u.1 u.2 p pstar =
      (max (u.2 - ⟪u.1, p⟫) 0 - max (u.2 - ⟪u.1, pstar⟫) 0) -
        (⟪u.1, pstar⟫ - ⟪u.1, p⟫) * (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) :=
    fun u => Aux_OLPDual_l1.kn _ _ _
  have hI3' : Integrable (fun u : E m × ℝ =>
      (⟪u.1, pstar⟫ - ⟪u.1, p⟫) * (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0)) law := by
    have := hI3.neg
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.neg_apply]
    ring
  have hrel : ∫ u, (⟪u.1, pstar⟫ - ⟪u.1, p⟫) * (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) ∂law
      = -∫ u, (if u.2 > ⟪u.1, pstar⟫ then (1 : ℝ) else 0) * (⟪u.1, p⟫ - ⟪u.1, pstar⟫) ∂law := by
    rw [← integral_neg]
    congr 1
    funext u
    ring
  have hmaxD : Integrable (fun u : E m × ℝ =>
      max (u.2 - ⟪u.1, p⟫) 0 - max (u.2 - ⟪u.1, pstar⟫) 0) law := (hmaxI p).sub (hmaxI pstar)
  rw [hinner]
  simp_rw [hpt, hK]
  unfold f
  rw [integral_sub (integrable_const _) hI3, integral_const, probReal_univ, one_smul,
    integral_sub hmaxD hI3', integral_sub (hmaxI p) (hmaxI pstar), hrel,
    inner_sub_right]
  ring
