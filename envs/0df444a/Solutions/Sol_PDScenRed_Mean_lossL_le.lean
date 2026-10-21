-- Prove2me | solution 1 for PDScenRed.Mean.lossL_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:15:41.47113+00:00
-- url     : https://prove2.me/submissions/a711fc33-22c9-44eb-8832-728652d08ee9

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory PDScenRed.Mean

theorem solution {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ)
    (B : ℝ) (hB : ∀ z ∈ polytope P qv, ∀ i, |z i| ≤ B) :
    ∀ ξ ζ : EuclideanSpace ℝ (Fin d),
      lossL (polytope P qv) zsel ξ ζ ≤
          |SmartPTO.Fisher.xi (polytope P qv) (ξ - (2 : ℝ) • ζ)| + 2 * |⟪ζ, zsel ξ⟫_ℝ| ∧
        |SmartPTO.Fisher.xi (polytope P qv) (ξ - (2 : ℝ) • ζ)| + 2 * |⟪ζ, zsel ξ⟫_ℝ| ≤
          (∑ i, |(ξ - (2 : ℝ) • ζ) i| + 2 * ∑ i, |ζ i|) * B ∧
        (∑ i, |(ξ - (2 : ℝ) • ζ) i| + 2 * ∑ i, |ζ i|) * B ≤
          (∑ i, |ξ i| + 4 * ∑ i, |ζ i|) * B := by
  set Z := polytope P qv with hZ
  -- |⟪c, w⟫| ≤ B * ∑ |c i| for w ∈ Z
  have hin : ∀ (c w : EuclideanSpace ℝ (Fin d)), w ∈ Z → |⟪c, w⟫_ℝ| ≤ B * ∑ i, |c i| := by
    intro c w hw
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp only [RCLike.inner_apply, conj_trivial, abs_mul]
    calc |w i| * |c i| ≤ B * |c i| := by gcongr; exact hB w hw i
      _ = B * |c i| := rfl
  have hxi : ∀ c : EuclideanSpace ℝ (Fin d), |SmartPTO.Fisher.xi Z c| ≤ B * ∑ i, |c i| := by
    intro c
    obtain ⟨w0, hw0⟩ := hne
    have hbd : BddAbove ((fun w => ⟪c, w⟫_ℝ) '' Z) := by
      refine ⟨B * ∑ i, |c i|, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      exact (le_abs_self _).trans (hin c w hw)
    unfold SmartPTO.Fisher.xi
    rw [abs_le]
    constructor
    · have := le_csSup hbd ⟨w0, hw0, rfl⟩
      have h2 := (abs_le.mp (hin c w0 hw0)).1
      linarith
    · exact csSup_le ⟨_, w0, hw0, rfl⟩ (by
        rintro _ ⟨w, hw, rfl⟩
        exact (le_abs_self _).trans (hin c w hw))
  intro ξ ζ
  have hz := (hsel ξ).1
  have hζ : |⟪ζ, zsel ξ⟫_ℝ| ≤ B * ∑ i, |ζ i| := hin ζ _ hz
  have hBnn : 0 ≤ B ∨ (∀ i : Fin d, False) := by
    rcases isEmpty_or_nonempty (Fin d) with h | ⟨⟨i⟩⟩
    · right; exact fun i => isEmptyElim i
    · obtain ⟨w0, hw0⟩ := hne
      left
      exact (abs_nonneg _).trans (hB w0 hw0 i)
  refine ⟨?_, ?_, ?_⟩
  · unfold lossL
    have e : ⟪zsel ξ, ζ⟫_ℝ = ⟪ζ, zsel ξ⟫_ℝ := real_inner_comm _ _
    rw [e]
    have h1 : max (SmartPTO.Fisher.xi Z (ξ - (2:ℝ) • ζ)) 0 ≤ |SmartPTO.Fisher.xi Z (ξ - (2:ℝ) • ζ)| :=
      max_le (le_abs_self _) (abs_nonneg _)
    have h2 : max ⟪ζ, zsel ξ⟫_ℝ 0 ≤ |⟪ζ, zsel ξ⟫_ℝ| := max_le (le_abs_self _) (abs_nonneg _)
    linarith
  · have := hxi (ξ - (2:ℝ) • ζ)
    nlinarith
  · have hsub : ∑ i, |(ξ - (2 : ℝ) • ζ) i| ≤ ∑ i, |ξ i| + 2 * ∑ i, |ζ i| := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      calc |ξ i - 2 * ζ i| ≤ |ξ i| + |2 * ζ i| := abs_sub _ _
        _ = |ξ i| + 2 * |ζ i| := by rw [abs_mul]; norm_num
    rcases hBnn with h | h
    · nlinarith
    · rcases isEmpty_or_nonempty (Fin d) with he | ⟨⟨i⟩⟩
      · simp
      · exact (h i).elim
