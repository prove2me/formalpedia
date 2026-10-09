-- Prove2me | solution 1 for TroppMatrixConcentration.ch4_rademacher_mgf_cgf
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:11:11.535989+00:00
-- url     : https://prove2.me/submissions/7bcf9585-0bce-4d62-a5f3-b8f5d09b1980

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration
namespace Ch4Rad

variable {d : ℕ}

noncomputable def proj (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (i : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * Matrix.single i i 1 *
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)

lemma cfc_eq_sum (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (hA.eigenvalues i) • proj A hA i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.sum_single_eq_diagonal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : Matrix.single i i ((RCLike.ofReal ∘ f ∘ hA.eigenvalues) i : ℂ)
      = f (hA.eigenvalues i) • (Matrix.single i i (1 : ℂ)) := by
    rw [Matrix.smul_single]; simp [Complex.real_smul]
  rw [this, proj, Matrix.mul_smul, Matrix.smul_mul]

lemma matrixExp_smul_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

lemma integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : Ω → ℝ)
    (hs : ∀ t, Integrable (fun ω => Real.exp (t * s ω)) μ) :
    Integrable (fun ω => matrixExp (s ω • A)) μ ∧
    ∫ ω, matrixExp (s ω • A) ∂μ = cfc (fun t => mgf s μ t) A := by
  have h : (fun ω => matrixExp (s ω • A)) =
      fun ω => ∑ i, Real.exp (hA.eigenvalues i * s ω) • proj A hA i := by
    funext ω
    rw [matrixExp_smul_eq A hA, cfc_eq_sum A hA]
    simp only [mul_comm]
  rw [h]
  refine ⟨integrable_finsetSum _ (fun i _ => (hs _).smul_const _), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hs _).smul_const _), cfc_eq_sum A hA]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_const]
  rfl


lemma smul_sq_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    c • A ^ 2 = cfc (fun x => c * x ^ 2) A := by
  rw [cfc_const_mul c (fun x : ℝ => x ^ 2) A, cfc_pow_id A 2 hA.isSelfAdjoint]

lemma matrixExp_smul_sq_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    matrixExp (c • A ^ 2) = cfc (fun x => Real.exp (c * x ^ 2)) A := by
  rw [matrixExp_smul_eq (A ^ 2) (hA.pow 2) c,
    ← cfc_comp_pow (fun y => Real.exp (c * y)) 2 A (by fun_prop) hA.isSelfAdjoint]

end Ch4Rad
end TroppMatrixConcentration

open TroppMatrixConcentration

lemma Ch4Rad.integrable_twoPoint (f : ℝ → ℝ) :
    Integrable f ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
  Integrable.add_measure (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
    (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hMeas : Measurable g) (hLaw : rademacherLaw μ g) (θ : ℝ) :
    loewnerLE (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) (matrixExp ((θ ^ 2 / 2) • A ^ 2)) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ)) ((θ ^ 2 / 2) • A ^ 2) := by
  have hs : ∀ t, Integrable (fun ω => Real.exp (t * (θ * g ω))) μ := by
    intro t
    have h1 := Ch4Rad.integrable_twoPoint (fun x => Real.exp (t * θ * x))
    rw [rademacherLaw] at hLaw
    rw [← hLaw] at h1
    have h2 := (integrable_map_measure (by fun_prop) hMeas.aemeasurable).mp h1
    simpa [Function.comp_def, mul_assoc] using h2
  have hmgf : ∀ t, mgf g μ t = Real.cosh t := by
    intro t
    have h1 := integral_map (μ := μ) hMeas.aemeasurable (f := fun x => Real.exp (t * x))
      (by fun_prop)
    rw [mgf, ← h1, hLaw, integral_add_measure, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, Real.cosh_eq]
    · simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul,
        mul_one, mul_neg]
      ring
    · exact Integrable.smul_measure (integrable_dirac (by simp)) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp)) (by simp)
  have hint : (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = cfc (fun x => Real.cosh (θ * x)) A := by
    rw [(Ch4Rad.integral_eq μ A hA (fun ω => θ * g ω) hs).2]
    congr 1
    funext x
    rw [mgf_const_mul, hmgf]
  have hpt : ∀ x : ℝ, Real.cosh (θ * x) ≤ Real.exp (θ ^ 2 / 2 * x ^ 2) := by
    intro x
    calc Real.cosh (θ * x) ≤ Real.exp ((θ * x) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = Real.exp (θ ^ 2 / 2 * x ^ 2) := by congr 1; ring
  constructor
  · rw [loewnerLE, ← Matrix.le_iff, hint, Ch4Rad.matrixExp_smul_sq_eq A hA]
    exact cfc_mono (fun x _ => hpt x)
  · rw [loewnerLE, ← Matrix.le_iff, hint, Ch4Rad.smul_sq_eq A hA, matrixLog,
      ← cfc_comp' Real.log (fun x => Real.cosh (θ * x)) A
        (Real.continuousOn_log.mono (by
          rintro _ ⟨x, _, rfl⟩
          exact (Real.cosh_pos _).ne'))]
    refine cfc_mono (fun x _ => ?_) ?_
    · calc Real.log (Real.cosh (θ * x)) ≤ Real.log (Real.exp (θ ^ 2 / 2 * x ^ 2)) :=
            Real.log_le_log (Real.cosh_pos _) (hpt x)
        _ = θ ^ 2 / 2 * x ^ 2 := Real.log_exp _
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun x => Real.cosh (θ * x)).continuousOn
        (fun x _ => (Real.cosh_pos _).ne'))
