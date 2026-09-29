-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.joint_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:51:10.913479+00:00
-- url     : https://prove2.me/submissions/076acd1e-35f0-4a36-9276-52d70d541f20

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

lemma aux_jcvx_integrable {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hM.isProb
  exact (((integrable_const y).sub hM.integrable).pos_part.const_mul h).add
    ((hM.integrable.sub (integrable_const y)).pos_part.const_mul p)

lemma aux_jcvx_pt {h p a b y1 y2 x : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    h * max (a * y1 + b * y2 - x) 0 + p * max (x - (a * y1 + b * y2)) 0 ≤
      a * (h * max (y1 - x) 0 + p * max (x - y1) 0) +
        b * (h * max (y2 - x) 0 + p * max (x - y2) 0) := by
  have e1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
    apply max_le
    · have : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
    apply max_le
    · have : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have f1 := mul_le_mul_of_nonneg_left e1 hh
  have f2 := mul_le_mul_of_nonneg_left e2 hp
  nlinarith [f1, f2]

lemma aux_jcvx_convex {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [newsvendorCost, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_jcvx_integrable hM y1).const_mul a)
      ((aux_jcvx_integrable hM y2).const_mul b)]
  apply integral_mono (aux_jcvx_integrable hM _)
    (((aux_jcvx_integrable hM y1).const_mul a).add ((aux_jcvx_integrable hM y2).const_mul b))
  intro x
  exact aux_jcvx_pt hM.h_pos.le hM.p_pos.le ha hb hab

lemma aux_jcvx_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) := by
  have := (aux_jcvx_convex hM).continuousOn isOpen_univ
  exact continuousOn_univ.mp this

lemma aux_jcvx_repr {G : ℝ → ℝ} (lam K Q r : ℝ) (hQ : 0 < Q) :
    qrCost G lam K Q r = lam * K * Q⁻¹ + ∫ u in (0 : ℝ)..1, G (Q * u + r) := by
  rw [intervalIntegral.integral_comp_mul_add (fun u => G u) hQ.ne' r]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul, qrCost]
  rw [add_comm Q r]
  field_simp

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

open MeasureTheory Filter Topology

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
      (fun z : ℝ × ℝ => qrCost (newsvendorCost μ h p) lam K z.1 z.2) := by
  set G := newsvendorCost μ h p with hGdef
  have hGc : Continuous G := aux_jcvx_cont hM
  have hGcv : ConvexOn ℝ Set.univ G := aux_jcvx_convex hM
  have hii : ∀ Q r : ℝ, IntervalIntegrable (fun u => G (Q * u + r)) volume 0 1 := by
    intro Q r
    exact (hGc.comp ((continuous_const.mul continuous_id).add continuous_const)).intervalIntegrable _ _
  refine ⟨(convex_Ioi 0).prod convex_univ, ?_⟩
  rintro ⟨Q1, r1⟩ ⟨hQ1, -⟩ ⟨Q2, r2⟩ ⟨hQ2, -⟩ a b ha hb hab
  simp only [Set.mem_Ioi] at hQ1 hQ2
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hQ : 0 < a * Q1 + b * Q2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hQ1, mul_nonneg hb hQ2.le]
    · subst ha'
      have : b = 1 := by linarith
      subst this
      simpa using hQ2
  rw [aux_jcvx_repr lam K _ _ hQ, aux_jcvx_repr lam K _ _ hQ1, aux_jcvx_repr lam K _ _ hQ2]
  have hinv : (a * Q1 + b * Q2)⁻¹ ≤ a * Q1⁻¹ + b * Q2⁻¹ := by
    have := (convexOn_zpow (𝕜 := ℝ) (-1)).2 (Set.mem_Ioi.mpr hQ1) (Set.mem_Ioi.mpr hQ2) ha hb hab
    simpa [zpow_neg_one, smul_eq_mul] using this
  have hint : (∫ u in (0 : ℝ)..1, G ((a * Q1 + b * Q2) * u + (a * r1 + b * r2))) ≤
      a * (∫ u in (0 : ℝ)..1, G (Q1 * u + r1)) + b * (∫ u in (0 : ℝ)..1, G (Q2 * u + r2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hii Q1 r1).const_mul a) ((hii Q2 r2).const_mul b)]
    apply intervalIntegral.integral_mono_on zero_le_one (hii _ _)
      (((hii Q1 r1).const_mul a).add ((hii Q2 r2).const_mul b))
    intro u _
    have := hGcv.2 (Set.mem_univ (Q1 * u + r1)) (Set.mem_univ (Q2 * u + r2)) ha hb hab
    simp only [smul_eq_mul] at this
    have e : (a * Q1 + b * Q2) * u + (a * r1 + b * r2) = a * (Q1 * u + r1) + b * (Q2 * u + r2) := by
      ring
    rw [e]
    exact this
  have hlk : 0 ≤ lam * K := mul_nonneg hM.lam_pos.le hK.le
  have := mul_le_mul_of_nonneg_left hinv hlk
  nlinarith [this, hint]
