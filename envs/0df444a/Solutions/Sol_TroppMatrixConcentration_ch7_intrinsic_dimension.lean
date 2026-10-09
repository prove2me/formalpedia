-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_intrinsic_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:32:36.562842+00:00
-- url     : https://prove2.me/submissions/6563acb9-34d9-43a8-88ce-a4576cee6380

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

lemma ch7_intrinsic_dimension_traceFunction_eq_sum {d : ℕ} (φ : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

lemma ch7_intrinsic_dimension_eig_le_norm {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues i ≤ spectralNorm A := by
  have h := spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
  exact (le_abs_self _).trans (by simpa [spectralNorm] using h)

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {d : ℕ} [NeZero d]
    (φ : ℝ → ℝ) (hConvex : ConvexOn ℝ (Set.Ici 0) φ) (hZero : φ 0 = 0)
    (A : Matrix (Fin d) (Fin d) ℂ) (hPSD : A.PosSemidef) :
    traceFunction φ A ≤ intrinsicDimension A * φ (spectralNorm A) := by
  have hA : A.IsHermitian := hPSD.isHermitian
  rw [ch7_intrinsic_dimension_traceFunction_eq_sum φ A hA]
  have htr : (Matrix.trace A).re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := fun i => hPSD.eigenvalues_nonneg i
  have hle : ∀ i, hA.eigenvalues i ≤ spectralNorm A :=
    ch7_intrinsic_dimension_eig_le_norm A hA
  set N := spectralNorm A with hN
  rw [intrinsicDimension, ← hN, htr]
  have hN0 : 0 ≤ N := le_trans (hnn ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩) (hle _)
  rcases hN0.eq_or_lt with h0 | hpos
  · have : ∀ i, hA.eigenvalues i = 0 := fun i => le_antisymm (h0 ▸ hle i) (hnn i)
    simp [this, hZero, ← h0]
  · have key : ∀ i, φ (hA.eigenvalues i) ≤ (hA.eigenvalues i / N) * φ N := by
      intro i
      set x := hA.eigenvalues i
      have hb0 : 0 ≤ x / N := div_nonneg (hnn i) hpos.le
      have hb1 : x / N ≤ 1 := (div_le_one hpos).mpr (hle i)
      have h := hConvex.2 (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hpos.le)
        (by linarith : (0:ℝ) ≤ 1 - x / N) hb0 (by ring : 1 - x / N + x / N = 1)
      have hx : (1 - x / N) • (0 : ℝ) + (x / N) • N = x := by
        simp [smul_eq_mul]; field_simp
      rw [hx, hZero] at h
      simpa [smul_eq_mul] using h
    calc ∑ i, φ (hA.eigenvalues i) ≤ ∑ i, (hA.eigenvalues i / N) * φ N :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = (∑ i, hA.eigenvalues i) / N * φ N := by
          rw [← Finset.sum_mul, Finset.sum_div]
