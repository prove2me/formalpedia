-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P47.induced_statistical_joint_convexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:43:27.31698+00:00
-- url     : https://prove2.me/submissions/86561b39-9c9f-4a4d-88cc-e60f50b312de

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

open scoped MatrixOrder ComplexOrder in
theorem g52c_trace_mul_psd_nonneg {d : ℕ} (M ρ : Mat d) (hM : M.PosSemidef)
    (hρ : ρ.PosSemidef) : 0 ≤ (M * ρ).trace.re := by
  have h0 : 0 ≤ ρ := hρ.nonneg
  have hS2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ h0
  have hSa : IsSelfAdjoint (CFC.sqrt ρ) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hSh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hSa.star_eq
  have htr : (M * ρ).trace = (CFC.sqrt ρ * M * (CFC.sqrt ρ)ᴴ).trace := by
    rw [hSh]
    conv_lhs => rw [← hS2, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [htr]
  exact (Complex.nonneg_iff.mp (hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)).trace_nonneg).1

theorem g52c_born_prob {d n : ℕ} (A : Measurement d n) (hA : IsPOVM A) (ρ : Mat d)
    (hρ : IsDensityMatrix ρ) : IsProbability (born A ρ) := by
  refine ⟨fun x => g52c_trace_mul_psd_nonneg _ _ (hA.1 x) hρ.1, ?_⟩
  simp only [born, effectProb]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hA.2, Matrix.one_mul, hρ.2,
    Complex.one_re]

theorem g52c_born_mixture {d n k : ℕ} (p : Fin k → ℝ) (C : Fin k → Measurement d n) (ρ : Mat d) :
    born (mixture p C) ρ = fun x => ∑ j, p j * born (C j) ρ x := by
  funext x
  simp only [born, effectProb, mixture, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end QAlgorithms.Papers.Independent.Information100.P47

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P47 in
theorem solution (delta : StatisticalDistance)
    (hC : StatisticalJointConvex delta) : JointConvex (inducedDistance delta) := by
  intro d n k hd hn p hp A B hA hB
  simp only [inducedDistance]
  apply iSup_le
  intro ρ
  rw [g52c_born_mixture, g52c_born_mixture]
  refine (hC n k hn p hp (fun j => born (A j) ρ.val) (fun j => born (B j) ρ.val)
    (fun j => g52c_born_prob _ (hA j) _ ρ.2) (fun j => g52c_born_prob _ (hB j) _ ρ.2)).trans ?_
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact le_iSup (fun ρ' : {rho : Mat d // IsDensityMatrix rho} =>
    delta n (born (A j) ρ'.val) (born (B j) ρ'.val)) ρ

end
