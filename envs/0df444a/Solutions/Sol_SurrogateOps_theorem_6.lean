-- Prove2me | solution 1 for SurrogateOps.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:21:53.662795+00:00
-- url     : https://prove2.me/submissions/4968dee7-15c8-4a62-a4ea-c5b9d60998b5

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear

namespace Aux_SurrogateOps_theorem_6

theorem core (a1 a2 b1 b2 Δ Δbar N1 N2 NF k1 k2 M1 M2 T1 T2 : ℝ)
    (hΔ : 0 < Δ) (hΔle : Δ ≤ Δbar) (hNF : NF = min N1 N2) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (ha1 : |a1| ≤ M1) (ha2 : |a2| ≤ M2) (hb1 : |b1| ≤ T1) (hb2 : |b2| ≤ T2)
    (h1 : |a1 - b1| ≤ k1 * Δ ^ N1) (h2 : |a2 - b2| ≤ k2 * Δ ^ N2) :
    |a1 * a2 - b1 * b2| ≤ min (T2 * k1 * Δbar ^ (N1 - NF) + M1 * k2 * Δbar ^ (N2 - NF))
      (M2 * k1 * Δbar ^ (N1 - NF) + T1 * k2 * Δbar ^ (N2 - NF)) * Δ ^ NF := by
  have hP : 0 ≤ Δ ^ NF := Real.rpow_nonneg hΔ.le _
  have hd1 : 0 ≤ N1 - NF := by rw [hNF]; linarith [min_le_left N1 N2]
  have hd2 : 0 ≤ N2 - NF := by rw [hNF]; linarith [min_le_right N1 N2]
  have e1 : Δ ^ N1 = Δ ^ NF * Δ ^ (N1 - NF) := by
    rw [← Real.rpow_add hΔ]; congr 1; ring
  have e2 : Δ ^ N2 = Δ ^ NF * Δ ^ (N2 - NF) := by
    rw [← Real.rpow_add hΔ]; congr 1; ring
  have r1 : Δ ^ (N1 - NF) ≤ Δbar ^ (N1 - NF) := Real.rpow_le_rpow hΔ.le hΔle hd1
  have r2 : Δ ^ (N2 - NF) ≤ Δbar ^ (N2 - NF) := Real.rpow_le_rpow hΔ.le hΔle hd2
  have u1 : 0 ≤ Δ ^ (N1 - NF) := Real.rpow_nonneg hΔ.le _
  have u2 : 0 ≤ Δ ^ (N2 - NF) := Real.rpow_nonneg hΔ.le _
  have hT1 : 0 ≤ T1 := le_trans (abs_nonneg _) hb1
  have hT2 : 0 ≤ T2 := le_trans (abs_nonneg _) hb2
  have hM1 : 0 ≤ M1 := le_trans (abs_nonneg _) ha1
  have hM2 : 0 ≤ M2 := le_trans (abs_nonneg _) ha2
  rw [e1] at h1
  rw [e2] at h2
  have hq1 : 0 ≤ k1 * (Δ ^ NF * Δ ^ (N1 - NF)) := mul_nonneg hk1 (mul_nonneg hP u1)
  have hq2 : 0 ≤ k2 * (Δ ^ NF * Δ ^ (N2 - NF)) := mul_nonneg hk2 (mul_nonneg hP u2)
  have A1 := mul_le_mul h1 hb2 (abs_nonneg _) hq1
  have A2 := mul_le_mul ha1 h2 (abs_nonneg _) hM1
  have B1 := mul_le_mul h1 ha2 (abs_nonneg _) hq1
  have B2 := mul_le_mul hb1 h2 (abs_nonneg _) hT1
  have tri1 : |a1 * a2 - b1 * b2| ≤ |a1 - b1| * |b2| + |a1| * |a2 - b2| := by
    have h : a1 * a2 - b1 * b2 = (a1 - b1) * b2 + a1 * (a2 - b2) := by ring
    rw [h, ← abs_mul, ← abs_mul]
    exact abs_add_le _ _
  have tri2 : |a1 * a2 - b1 * b2| ≤ |a1 - b1| * |a2| + |b1| * |a2 - b2| := by
    have h : a1 * a2 - b1 * b2 = (a1 - b1) * a2 + b1 * (a2 - b2) := by ring
    rw [h, ← abs_mul, ← abs_mul]
    exact abs_add_le _ _
  have m1 := mul_le_mul_of_nonneg_left r1 (mul_nonneg (mul_nonneg hk1 hT2) hP)
  have m2 := mul_le_mul_of_nonneg_left r2 (mul_nonneg (mul_nonneg hk2 hM1) hP)
  have m3 := mul_le_mul_of_nonneg_left r1 (mul_nonneg (mul_nonneg hk1 hM2) hP)
  have m4 := mul_le_mul_of_nonneg_left r2 (mul_nonneg (mul_nonneg hk2 hT1) hP)
  rw [min_mul_of_nonneg _ _ hP]
  apply le_min
  · linarith
  · linarith

end Aux_SurrogateOps_theorem_6

open SurrogateOps Aux_SurrogateOps_theorem_6 in
theorem solution {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ Mf₁ Mf₂ Mft₁ Mft₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hMf₁ : ∀ x ∈ Metric.closedBall x0 Δbar, |f₁ x| ≤ Mf₁)
    (hMf₂ : ∀ x ∈ Metric.closedBall x0 Δbar, |f₂ x| ≤ Mf₂)
    (hNF : NF = min N₁ N₂)
    (hK : K = min
      (Mft₂ * κ₁ * Δbar ^ (N₁ - NF) + Mf₁ * κ₂ * Δbar ^ (N₂ - NF))
      (Mf₂ * κ₁ * Δbar ^ (N₁ - NF) + Mft₁ * κ₂ * Δbar ^ (N₂ - NF))) :
    (FunAccAt f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccAt f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |fm₁ Δ x0| ≤ Mft₁) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |fm₂ Δ x0| ≤ Mft₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar,
        |f₁ x0 * f₂ x0 - fm₁ Δ x0 * fm₂ Δ x0| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccAt (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ) ∧
    (FunAccNear f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccNear f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm₁ Δ x| ≤ Mft₁) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm₂ Δ x| ≤ Mft₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |f₁ x * f₂ x - fm₁ Δ x * fm₂ Δ x| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccNear (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ) := by
  have hx0 : x0 ∈ Metric.closedBall x0 Δbar := Metric.mem_closedBall_self hΔbar.le
  have hΔbarI : Δbar ∈ Set.Ioc 0 Δbar := ⟨hΔbar, le_rfl⟩
  have hMf1 : 0 ≤ Mf₁ := le_trans (abs_nonneg _) (hMf₁ x0 hx0)
  have hMf2 : 0 ≤ Mf₂ := le_trans (abs_nonneg _) (hMf₂ x0 hx0)
  have hV1 : 0 ≤ Δbar ^ (N₁ - NF) := Real.rpow_nonneg hΔbar.le _
  have hV2 : 0 ≤ Δbar ^ (N₂ - NF) := Real.rpow_nonneg hΔbar.le _
  constructor
  · rintro ⟨hN1, hk1, hb1⟩ ⟨hN2, hk2, hb2⟩ hT1 hT2
    have hMt1 : 0 ≤ Mft₁ := le_trans (abs_nonneg _) (hT1 Δbar hΔbarI)
    have hMt2 : 0 ≤ Mft₂ := le_trans (abs_nonneg _) (hT2 Δbar hΔbarI)
    have bound : ∀ Δ ∈ Set.Ioc 0 Δbar,
        |f₁ x0 * f₂ x0 - fm₁ Δ x0 * fm₂ Δ x0| ≤ K * Δ ^ NF := by
      intro Δ hΔ
      rw [hK]
      exact core _ _ _ _ Δ Δbar N₁ N₂ NF κ₁ κ₂ Mf₁ Mf₂ Mft₁ Mft₂ hΔ.1 hΔ.2 hNF hk1 hk2
        (hMf₁ x0 hx0) (hMf₂ x0 hx0) (hT1 Δ hΔ) (hT2 Δ hΔ) (hb1 Δ hΔ) (hb2 Δ hΔ)
    have hNF0 : 0 ≤ NF := by rw [hNF]; exact le_min hN1 hN2
    have hK0 : 0 ≤ K := by
      rw [hK]
      apply le_min
      · have := mul_nonneg (mul_nonneg hMt2 hk1) hV1
        have := mul_nonneg (mul_nonneg hMf1 hk2) hV2
        linarith
      · have := mul_nonneg (mul_nonneg hMf2 hk1) hV1
        have := mul_nonneg (mul_nonneg hMt1 hk2) hV2
        linarith
    exact ⟨bound, K, hNF0, hK0, bound⟩
  · rintro ⟨hN1, hk1, hb1⟩ ⟨hN2, hk2, hb2⟩ hT1 hT2
    have hMt1 : 0 ≤ Mft₁ := le_trans (abs_nonneg _) (hT1 Δbar hΔbarI x0 hx0)
    have hMt2 : 0 ≤ Mft₂ := le_trans (abs_nonneg _) (hT2 Δbar hΔbarI x0 hx0)
    have bound : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |f₁ x * f₂ x - fm₁ Δ x * fm₂ Δ x| ≤ K * Δ ^ NF := by
      intro Δ hΔ x hx
      have hx' : x ∈ Metric.closedBall x0 Δbar := Metric.closedBall_subset_closedBall hΔ.2 hx
      rw [hK]
      exact core _ _ _ _ Δ Δbar N₁ N₂ NF κ₁ κ₂ Mf₁ Mf₂ Mft₁ Mft₂ hΔ.1 hΔ.2 hNF hk1 hk2
        (hMf₁ x hx') (hMf₂ x hx') (hT1 Δ hΔ x hx) (hT2 Δ hΔ x hx) (hb1 Δ hΔ x hx) (hb2 Δ hΔ x hx)
    have hNF0 : 0 ≤ NF := by rw [hNF]; exact le_min hN1 hN2
    have hK0 : 0 ≤ K := by
      rw [hK]
      apply le_min
      · have := mul_nonneg (mul_nonneg hMt2 hk1) hV1
        have := mul_nonneg (mul_nonneg hMf1 hk2) hV2
        linarith
      · have := mul_nonneg (mul_nonneg hMf2 hk1) hV1
        have := mul_nonneg (mul_nonneg hMt1 hk2) hV2
        linarith
    exact ⟨bound, K, hNF0, hK0, bound⟩
