-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P28.qubit_unital_part_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:39.444808+00:00
-- url     : https://prove2.me/submissions/48b9ba4c-d435-41ba-907c-8395cf2d34e3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

lemma g52_trace_real {n : Type*} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    star A.trace = A.trace := by
  have h := hA.trace_nonneg
  rw [Complex.star_def, Complex.conj_eq_iff_im]; exact (Complex.nonneg_iff.mp h).2.symm

lemma g52_adj_psd {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) :
    (A.trace • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  refine ⟨?_, fun x => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hA.1.eq, g52_trace_real (Matrix.posSemidef_iff_dotProduct_mulVec.mpr hA)]
  · let y : Fin 2 → ℂ := ![star (x 1), -star (x 0)]
    have := hA.2 y
    convert this using 1
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.trace, y, Matrix.one_apply, Matrix.sub_apply]
    ring

open QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30
  QAlgorithms.Papers.Independent.Frontier30.P28 in
/-- Unnumbered qubit result proved by the Bloch-ball argument,
source PDF p.6, §III.A: positivity of the constructed unital part is a conclusion. -/
theorem solution
    (T : Lin 2 2) (hpos : IsPositiveMap T) (htrace : TracePreserving T) :
    IsPositiveMap (unitalPart T) := by
  intro A hA
  set t := A.trace with ht
  have hB := hpos A hA
  have hadj := g52_adj_psd hA
  have hC := hpos _ hadj
  have htrC : (T (t • 1 - A)).trace = t := by
    rw [htrace, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp; ring
  have hD := g52_adj_psd hC
  rw [htrC] at hD
  have key : unitalPart T A = (2 : ℂ)⁻¹ • (T A + (t • 1 - T (t • 1 - A))) := by
    simp only [unitalPart, traceTerm, nonunitalOffset, LinearMap.sub_apply, LinearMap.coe_mk,
      AddHom.coe_mk, map_sub, map_smul]
    rw [← ht]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    ring
  rw [key]
  refine (hB.add hD).smul ?_
  rw [Complex.le_def]; norm_num
