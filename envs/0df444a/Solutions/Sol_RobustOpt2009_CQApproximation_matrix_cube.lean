-- Prove2me | solution 1 for RobustOpt2009.CQApproximation.matrix_cube
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:34:05.084035+00:00
-- url     : https://prove2.me/submissions/82b80085-9c6c-400f-9928-4af6c7a524c3

import Definitions.Def_RobustOpt2009_CQApproximation_MixedCube
import Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_7_1_3

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

private lemma l2_opNorm_le_iff_operatorBound {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖M‖ ≤ r ↔ RobustOpt2009.CQApproximation.OperatorBound M r := by
  rw [Matrix.l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff hr]
  constructor
  · intro h v
    simpa [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h (WithLp.toLp 2 v)
  · intro h x
    simpa [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap',
      Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h x.ofLp

private lemma robust_iff {m p q : ℕ} (D : RobustOpt2009.CQApproximation.CubeData m p q)
    {r : ℝ} (hr : 0 ≤ r) :
    (∀ (z : Fin p → ℝ) (Z : (j : Fin q) → Matrix (Fin (D.rowsL j)) (Fin (D.rowsR j)) ℝ),
      (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
      (D.B0 + (∑ i, z i • D.B i) +
        ∑ j, ((D.L j)ᵀ * Z j * D.R j + (D.R j)ᵀ * (Z j)ᵀ * D.L j)).PosSemidef) ↔
      D.Robust r := by
  unfold RobustOpt2009.CQApproximation.CubeData.Robust RobustOpt2009.CQApproximation.blockTerm
  constructor
  · intro h θ Θ hθ hΘ
    exact h θ Θ hθ fun j => (l2_opNorm_le_iff_operatorBound (Θ j) hr).mpr (hΘ j)
  · intro h z Z hz hZ
    exact h z Z hz fun j => (l2_opNorm_le_iff_operatorBound (Z j) hr).mp (hZ j)

private lemma envelope_iff {m p q : ℕ} (D : RobustOpt2009.CQApproximation.CubeData m p q)
    (ρ : ℝ) :
    (∃ (U : Fin p → Matrix (Fin m) (Fin m) ℝ)
      (V : Fin q → Matrix (Fin m) (Fin m) ℝ),
      (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
      (∀ i, (U i - D.B i).PosSemidef ∧ (U i + D.B i).PosSemidef) ∧
      (∀ j, ∀ Z : Matrix (Fin (D.rowsL j)) (Fin (D.rowsR j)) ℝ, ‖Z‖ ≤ 1 →
        (V j - ((D.L j)ᵀ * Z * D.R j + (D.R j)ᵀ * Zᵀ * D.L j)).PosSemidef) ∧
      (D.B0 - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef) ↔
      D.Envelope ρ := by
  unfold RobustOpt2009.CQApproximation.CubeData.Envelope RobustOpt2009.CQApproximation.blockTerm
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  constructor
  · rintro ⟨U, V, hU, hV, hUB, hVZ, hB0⟩
    exact ⟨U, V, hU, hV, hUB,
      fun j Θ hΘ => hVZ j Θ ((l2_opNorm_le_iff_operatorBound Θ h01).mpr hΘ), hB0⟩
  · rintro ⟨U, V, hU, hV, hUB, hVZ, hB0⟩
    exact ⟨U, V, hU, hV, hUB,
      fun j Z hZ => hVZ j Z ((l2_opNorm_le_iff_operatorBound Z h01).mp hZ), hB0⟩

open RobustOpt2009.CQApproximation in
theorem solution :
    ∃ ϑ : ℕ → ℝ, Monotone ϑ ∧ ϑ 2 = Real.pi / 2 ∧ ϑ 4 = 2 ∧
      (∀ μ : ℕ, 2 ≤ μ → ϑ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (m p q : ℕ), 0 < m → ∀ (D : CubeData m p q) (ρ : ℝ), 0 < ρ →
        (D.Envelope ρ → D.Robust ρ) ∧
        (p + q = 1 → (D.Envelope ρ ↔ D.Robust ρ)) ∧
        (∀ μ : ℕ, 2 ≤ μ → (∀ i, (D.B i).rank ≤ μ) →
          ¬ D.Envelope ρ → ¬ D.Robust (ϑ μ * ρ)) := by
  obtain ⟨θ, hmono, h2, h4, hbound, hmain⟩ := RobustOpt2009.SDPApproximation.theorem_7_1_3
  refine ⟨θ, hmono, h2, h4, hbound, ?_⟩
  intro m p q hm D ρ hρ
  obtain ⟨hba, h1, htight⟩ :=
    hmain m p q hm D.rowsL D.rowsR D.posL D.posR D.B0 D.B D.L D.R D.symm0 D.symm ρ hρ.le
  have henv := envelope_iff D ρ
  have hrob := robust_iff D hρ.le
  refine ⟨?_, ?_, ?_⟩
  · exact fun hE => hrob.mp (hba (henv.mpr hE))
  · intro hpq
    exact henv.symm.trans ((h1 hpq).trans hrob)
  · intro μ hμ hrank hnE
    have hθ_nonneg : 0 ≤ θ μ := by
      have h2le : θ 2 ≤ θ μ := hmono hμ
      rw [h2] at h2le
      exact le_trans (by positivity) h2le
    have hθρ_nonneg : 0 ≤ θ μ * ρ := mul_nonneg hθ_nonneg hρ.le
    have hrob_μ := robust_iff D hθρ_nonneg
    exact fun hR => htight μ hμ hrank (fun hb => hnE (henv.mp hb)) (hrob_μ.mpr hR)
