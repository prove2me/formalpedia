-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_50
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T12:47:14.82823+00:00
-- url     : https://prove2.me/submissions/a8a9c160-9b1b-4a2e-8b1f-ab60715e2642

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_55
import Theorems.Thm_QAOAE3Lin2_Typical_eq_49

open QAOAE3Lin2.Typical

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (γ : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ Real.pi / 2) :
    (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D) ≤
        avgD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) ∧
      avgD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) ≤
        (m : ℝ) / 2 * Real.sin γ := by
  have hsin : 0 ≤ Real.sin γ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hγ₀ (by linarith [Real.pi_pos])
  have hcos0 : 0 ≤ Real.cos γ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hγ₁⟩
  have hcos1 : Real.cos γ ≤ 1 := Real.cos_le_one γ
  -- the exponent attached to equation `i`
  let k : Fin m → ℕ := fun i =>
    QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 +
      QAOAE3Lin2.General.termCount tri i 2
  have hk : ∀ i, k i ≤ 3 * D := fun i => (eq_49 tri D htri hocc i γ).2
  -- (55) and linearity of the average, then (49) termwise
  have hkey : avgD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) =
      ∑ i : Fin m, (1 / 2) * Real.sin γ * Real.cos γ ^ k i := by
    have h1 : (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) =
        fun rhs => ∑ i, clauseTerm tri rhs i γ := by
      funext rhs
      rw [eq_55 tri rhs γ]
      ring
    rw [h1]
    simp only [avgD]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h49 := (eq_49 tri D htri hocc i γ).1
    simp only [avgD] at h49
    exact h49
  have hhalf : 0 ≤ (1 / 2 : ℝ) * Real.sin γ := mul_nonneg (by norm_num) hsin
  rw [hkey]
  constructor
  · calc (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D)
        = ∑ _i : Fin m, (1 / 2) * Real.sin γ * Real.cos γ ^ (3 * D) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ ∑ i : Fin m, (1 / 2) * Real.sin γ * Real.cos γ ^ k i :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hcos0 hcos1 (hk i)) hhalf)
  · calc ∑ i : Fin m, (1 / 2) * Real.sin γ * Real.cos γ ^ k i
        ≤ ∑ _i : Fin m, (1 / 2) * Real.sin γ * 1 :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (pow_le_one₀ hcos0 hcos1) hhalf)
      _ = (m : ℝ) / 2 * Real.sin γ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
