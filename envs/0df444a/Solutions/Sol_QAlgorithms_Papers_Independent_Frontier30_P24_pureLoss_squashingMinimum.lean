-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P24.pureLoss_squashingMinimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:48:16.048043+00:00
-- url     : https://prove2.me/submissions/baf405ac-1f31-4bc1-9e09-d230ed5062eb

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24

open QAlgorithms.Papers.Independent.Frontier30.P24
open Filter Set

noncomputable section

namespace X6P24s

/-- unnormalised entropy -/
def K (x : ℝ) : ℝ := (x + 1) * Real.log (x + 1) - x * Real.log x

theorem K_cont : Continuous K := by
  unfold K
  exact (Real.continuous_mul_log.comp (continuous_add_const 1)).sub Real.continuous_mul_log

theorem K_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt K (Real.log (x + 1) - Real.log x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y + 1) * Real.log (y + 1))
      (1 * Real.log (x + 1) + (x + 1) * (1 / (x + 1))) x := by
    have ha : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    have hb : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x :=
      ha.log (by linarith)
    exact ha.mul hb
  have h2 : HasDerivAt (fun y : ℝ => y * Real.log y) (1 * Real.log x + x * (1 / x)) x := by
    have hb : HasDerivAt Real.log (1 / x) x := by
      simpa [one_div] using Real.hasDerivAt_log hx.ne'
    exact (hasDerivAt_id x).mul hb
  have := h1.sub h2
  refine this.congr_deriv ?_
  field_simp
  ring

/-- G x = K'(x) - K'(x + δ) -/
def G (δ x : ℝ) : ℝ := (Real.log (x + 1) - Real.log x) - (Real.log (x + δ + 1) - Real.log (x + δ))

theorem G_anti (δ : ℝ) (hδ : 0 ≤ δ) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : G δ y ≤ G δ x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hG : ∀ z, 0 < z → G δ z =
      Real.log ((z + 1) * (z + δ) / (z * (z + δ + 1))) := by
    intro z hz
    rw [G, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hG x hx, hG y hy]
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hP : x * (x + δ + 1) ≤ y * (y + δ + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hP hδ]

end X6P24s

open X6P24s

theorem solution
    (eta photonNumber : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hphotonNumber : 0 ≤ photonNumber) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      pureLossSquashingBound eta photonNumber s =
        pureLossSquashingBound eta photonNumber (1 - s)) ∧
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (pureLossSquashingBound eta photonNumber) ∧
    IsLeast ((pureLossSquashingBound eta photonNumber) '' Set.Icc (0 : ℝ) 1)
      (pureLossSymmetricBound eta photonNumber) ∧
    pureLossSquashingBound eta photonNumber (1 / 2) =
      pureLossSymmetricBound eta photonNumber := by
  set N := photonNumber with hN
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ := (1 - eta) * N with hκ
  set δ := eta * N with hδ
  have hκ0 : 0 ≤ κ := mul_nonneg (by linarith) hphotonNumber
  have hδ0 : 0 ≤ δ := mul_nonneg heta0 hphotonNumber
  -- normal form
  have hform : ∀ s, pureLossSquashingBound eta N s =
      (K (κ * (1 - s) + δ) + K (κ * s + δ) - K (κ * s) - K (κ * (1 - s))) / (2 * Real.log 2) := by
    intro s
    simp only [pureLossSquashingBound, bosonicEntropy, K]
    rw [show (1 - s + eta * s) * N = κ * (1 - s) + δ by rw [hκ, hδ]; ring,
      show (s + eta * (1 - s)) * N = κ * s + δ by rw [hκ, hδ]; ring,
      show s * (1 - eta) * N = κ * s by rw [hκ]; ring,
      show (1 - s) * (1 - eta) * N = κ * (1 - s) by rw [hκ]; ring]
    field_simp
  have hsym : ∀ s, pureLossSquashingBound eta N s = pureLossSquashingBound eta N (1 - s) := by
    intro s
    rw [hform, hform, sub_sub_cancel]
    ring_nf
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (pureLossSquashingBound eta N) := by
    rcases hκ0.lt_or_eq with hκp | hκz
    · have hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt
          (fun s => (K (κ * (1 - s) + δ) + K (κ * s + δ) - K (κ * s) - K (κ * (1 - s))) /
            (2 * Real.log 2))
          (κ / (2 * Real.log 2) * (G δ (κ * (1 - s)) - G δ (κ * s))) s := by
        intro s hs
        have hu0 : 0 < κ * (1 - s) := mul_pos hκp (by linarith [hs.2])
        have hw0 : 0 < κ * s := mul_pos hκp hs.1
        have hu : HasDerivAt (fun s : ℝ => κ * (1 - s)) (-κ) s :=
          (((hasDerivAt_id s).const_sub 1).const_mul κ).congr_deriv (by simp)
        have hw : HasDerivAt (fun s : ℝ => κ * s) κ s :=
          ((hasDerivAt_id s).const_mul κ).congr_deriv (by simp)
        have h1 := (K_deriv _ (by linarith : 0 < κ * (1 - s) + δ)).comp s (hu.add_const δ)
        have h2 := (K_deriv _ (by linarith : 0 < κ * s + δ)).comp s (hw.add_const δ)
        have h3 := (K_deriv _ hw0).comp s hw
        have h4 := (K_deriv _ hu0).comp s hu
        have := (((h1.add h2).sub h3).sub h4).div_const (2 * Real.log 2)
        refine this.congr_deriv ?_
        simp only [G]
        ring_nf
      rw [funext hform]
      apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
      · apply Continuous.continuousOn
        have := K_cont
        fun_prop
      · intro s hs
        rw [interior_Icc] at hs
        exact (hd s hs).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro s1 hs1 s2 hs2 h12
        rw [(hd s1 hs1).deriv, (hd s2 hs2).deriv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have e1 := G_anti δ hδ0 (κ * (1 - s2)) (κ * (1 - s1)) (mul_pos hκp (by linarith [hs2.2]))
          (mul_le_mul_of_nonneg_left (by linarith) hκ0)
        have e2 := G_anti δ hδ0 (κ * s1) (κ * s2) (mul_pos hκp hs1.1)
          (mul_le_mul_of_nonneg_left h12 hκ0)
        linarith
    · have hc : pureLossSquashingBound eta N = fun _ => (K δ + K δ - K 0 - K 0) / (2 * Real.log 2) := by
        funext s
        rw [hform, ← hκz]
        simp
      rw [hc]
      exact convexOn_const _ (convex_Icc 0 1)
  have hhalf : pureLossSquashingBound eta N (1 / 2) = pureLossSymmetricBound eta N := by
    simp only [pureLossSquashingBound, pureLossSymmetricBound]
    rw [show (1 - 1 / 2 + eta * (1 / 2)) * N = (1 + eta) * N / 2 by ring,
      show (1 / 2 + eta * (1 - 1 / 2)) * N = (1 + eta) * N / 2 by ring,
      show 1 / 2 * (1 - eta) * N = (1 - eta) * N / 2 by ring,
      show (1 - 1 / 2) * (1 - eta) * N = (1 - eta) * N / 2 by ring]
    ring
  refine ⟨fun s _ => hsym s, hconv, ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, hhalf⟩, ?_⟩, hhalf⟩
  rintro y ⟨s, hs, rfl⟩
  rw [← hhalf]
  have h1s : 1 - s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := hconv.2 hs h1s (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • s + (1 / 2 : ℝ) • (1 - s) = 1 / 2 by simp [smul_eq_mul]; ring,
    ← hsym s] at this
  simp only [smul_eq_mul] at this
  linarith
