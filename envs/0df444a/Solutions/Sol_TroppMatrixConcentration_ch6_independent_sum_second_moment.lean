-- Prove2me | solution 1 for TroppMatrixConcentration.ch6_independent_sum_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:35:11.668009+00:00
-- url     : https://prove2.me/submissions/bd0afb40-6878-43b8-9e45-a88dbbfc1fee

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Bilinear

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

/-- Matrix multiplication as a continuous real-bilinear map (L2 operator norms). -/
noncomputable def ch6isMulCLM (p q r : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin q) (Fin r) ℂ →L[ℝ] Matrix (Fin p) (Fin r) ℂ :=
  LinearMap.mkContinuous₂ (mulLinearMap ℝ) 1
    (fun A B => by simpa using Matrix.l2_opNorm_mul A B)

lemma ch6isMulCLM_apply (p q r : ℕ) (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    ch6isMulCLM p q r A B = A * B := by
  simp [ch6isMulCLM]

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n a b c N : ℕ}
    (X : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ)
    (f : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin a) (Fin b) ℂ)
    (g : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin b) (Fin c) ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hfL2 : ∀ k, MemLp (fun ω => f (X k ω)) 2 μ)
    (hgL2 : ∀ k, MemLp (fun ω => g (X k ω)) 2 μ)
    (hfMean : ∀ k, (∫ ω, f (X k ω) ∂μ) = 0) :
    (∫ ω, (∑ k, f (X k ω)) * (∑ k, g (X k ω)) ∂μ) =
      ∑ k, ∫ ω, f (X k ω) * g (X k ω) ∂μ := by
  classical
  have hint : ∀ j k, Integrable (fun ω => f (X j ω) * g (X k ω)) μ := by
    intro j k
    have hm : AEStronglyMeasurable (fun ω => f (X j ω) * g (X k ω)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) => A * B)
        (continuous_fst.matrix_mul continuous_snd) (hfL2 j).1 (hgL2 k).1
    have h1 := MemLp.of_bilin (p := 2) (q := 2) (r := 1)
      (fun (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) => A * B) 1
      (hfL2 j) (hgL2 k) hm
      (Filter.Eventually.of_forall fun ω => by simpa using Matrix.l2_opNNNorm_mul _ _)
    exact memLp_one_iff_integrable.1 h1
  have hcross : ∀ j k, j ≠ k → ∫ ω, f (X j ω) * g (X k ω) ∂μ = 0 := by
    intro j k hjk
    have hind : IndepFun (fun ω => f (X j ω)) (fun ω => g (X k ω)) μ :=
      (hIndep.indepFun hjk).comp hf hg
    have h2 := hind.integral_bilin ((hfL2 j).integrable one_le_two)
      ((hgL2 k).integrable one_le_two) (ch6isMulCLM a b c)
    simp only [ch6isMulCLM_apply] at h2
    rw [h2, hfMean j, Matrix.zero_mul]
  simp_rw [Matrix.sum_mul, Matrix.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum _ (fun k _ => hint j k)]
  rw [Finset.sum_eq_single j (fun k _ hkj => hcross j k (Ne.symm hkj)) (by simp)]
