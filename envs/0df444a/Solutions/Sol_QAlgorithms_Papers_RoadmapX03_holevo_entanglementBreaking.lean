-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapX03.holevo_entanglementBreaking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:08:18.996282+00:00
-- url     : https://prove2.me/submissions/baadf676-637b-445d-953d-f3f58f9c0894

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_holevo_kraus_and_reductions
import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate
open Matrix QAlgorithms

private def conditional {a d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun i j => (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace

private lemma block_sandwich {a d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (i j : Fin a) :
    ((Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T) * X *
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T)ᴴ).submatrix
        (fun t => (i,t)) (fun t => (j,t)) =
      T * X.submatrix (fun t => (i,t)) (fun t => (j,t)) * Tᴴ := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker']
  ext u v
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.submatrix_apply]

private lemma traceRight_psd {a d : ℕ}
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (hX : X.PosSemidef) :
    (traceRight X).PosSemidef := by
  have heq : traceRight X = ∑ t, X.submatrix (fun i => (i,t)) (fun i => (i,t)) := by
    ext i j
    simp [traceRight, Matrix.sum_apply, Matrix.submatrix]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun t _ => hX.submatrix _

private lemma conditional_psd {a d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.PosSemidef)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (hX : X.PosSemidef) :
    (conditional F X).PosSemidef := by
  let T := CFC.sqrt F
  have hT : T.IsHermitian := (CFC.sqrt_nonneg F).posSemidef.isHermitian
  have hTT : T * T = F := by simpa [T, pow_two] using CFC.sq_sqrt F hF.nonneg
  let B := Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) T
  have heq : conditional F X = traceRight (B * X * Bᴴ) := by
    ext i j
    change (F * X.submatrix (fun t => (i,t)) (fun t => (j,t))).trace =
      ((B * X * Bᴴ).submatrix (fun t => (i,t)) (fun t => (j,t))).trace
    rw [block_sandwich, hT.eq, Matrix.trace_mul_cycle, hTT]
  rw [heq]
  exact traceRight_psd _ (hX.mul_mul_conjTranspose_same B)

private lemma output_sum {a d m : ℕ}
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    idTensorSuperop (Entanglement.holevoMap R F) X =
      ∑ k, Matrix.kronecker (conditional (F k) X) (R k) := by
  ext p q
  simp [idTensorSuperop, Entanglement.holevoMap, conditional,
    Matrix.sum_apply, Matrix.submatrix]

private lemma psd_normalization {a : ℕ} (ha : 0 < a)
    (A : Matrix (Fin a) (Fin a) ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix B ∧ (A.trace.re : ℂ) • B = A := by
  have hr : (A.trace.re : ℂ) = A.trace := Complex.ext rfl hA.trace_nonneg.2
  by_cases hz : A.trace.re = 0
  · have hzero : A = 0 := hA.trace_eq_zero_iff.mp (by rw [← hr, hz]; rfl)
    let B : Matrix (Fin a) (Fin a) ℂ := ((a : ℝ)⁻¹ : ℂ) • 1
    refine ⟨B, ⟨?_, ?_⟩, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg a))
    · simp [B, Matrix.trace_smul, Matrix.trace_one, ne_of_gt ha]
    · simp [hzero]
  · refine ⟨((A.trace.re)⁻¹ : ℂ) • A, ⟨?_, ?_⟩, ?_⟩
    · exact hA.smul (by exact_mod_cast inv_nonneg.mpr hA.trace_nonneg.1)
    · rw [Matrix.trace_smul, smul_eq_mul, ← hr]
      simpa only [Complex.ofReal_re, Complex.ofReal_inv] using
        inv_mul_cancel₀ (show (A.trace.re : ℂ) ≠ 0 by exact_mod_cast hz)
    · simp only [smul_smul,
        mul_inv_cancel₀ (show (A.trace.re : ℂ) ≠ 0 by exact_mod_cast hz), one_smul]

private lemma output_decomposition {a d m : ℕ} (ha : 0 < a)
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (hX : X.PosSemidef) :
    ∃ w : Fin m → ℝ, ∃ B : Fin m → Matrix (Fin a) (Fin a) ℂ,
      (∀ k, 0 ≤ w k) ∧ (∀ k, IsDensityMatrix (B k) ∧ IsDensityMatrix (R k)) ∧
      idTensorSuperop (Entanglement.holevoMap R F) X =
        ∑ k, (w k : ℂ) • Matrix.kronecker (B k) (R k) := by
  have hp k := conditional_psd (F k) (hF k) X hX
  choose B hB hEq using fun k => psd_normalization ha (conditional (F k) X) (hp k)
  refine ⟨fun k => (conditional (F k) X).trace.re, B,
    (fun k => (hp k).trace_nonneg.1), (fun k => ⟨hB k, hR k⟩), ?_⟩
  rw [output_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hEq k]
  simp only [Matrix.kronecker, Matrix.smul_kronecker]

private lemma output_trace {a d m : ℕ}
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hPOVM : IsPOVM F)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    (idTensorSuperop (Entanglement.holevoMap R F) X).trace = X.trace := by
  rw [output_sum, Matrix.trace_sum]
  simp only [Matrix.kronecker, Matrix.trace_kronecker]
  simp_rw [(hR _).2, mul_one]
  change (∑ k, ∑ i, (F k * X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace) = _
  rw [Finset.sum_comm]
  have hi (i : Fin a) : (∑ k, (F k * X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace) =
      (X.submatrix (fun t => (i,t)) (fun t => (i,t))).trace := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hPOVM.2, Matrix.one_mul]
  simp_rw [hi]
  simp [Matrix.trace, Fintype.sum_prod_type, Matrix.submatrix_apply]

private lemma separable_density_of_trace_one {a d : ℕ} [Nonempty (Fin a)] [Nonempty (Fin d)]
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hs : Entanglement.IsSeparablePositive X) (ht : X.trace = 1) :
    Entanglement.IsSeparableDensity X := by
  rcases hs with ⟨q, w, A, B, hw, hAB, heq⟩
  refine ⟨q, w, A, B, hw, ?_, hAB, heq⟩
  have h := congrArg Matrix.trace heq
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.kronecker,
    Matrix.trace_kronecker, (hAB _).1.2, (hAB _).2.2, mul_one, smul_eq_mul] at h
  rw [ht] at h
  exact_mod_cast h.symm

private lemma holevo_channel {d m : ℕ} (hd : 0 < d)
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef) (hPOVM : IsPOVM F) :
    IsChannel (Entanglement.holevoMap R F) := by
  classical
  let e := EuclideanSpace.basisFun (Fin d) ℂ
  let K := Fin m × (Fin d × Fin d)
  let A := QAlgorithms.Papers.Independent.Independent1.P02.holevoKrausOperators R F e e
  let equiv := Fintype.equivFin K
  have h := (QAlgorithms.Papers.Independent.Independent1.P02.holevo_kraus_and_reductions d hd).1
    m R F hR hF e e
  refine ⟨Fintype.card K, fun i => A (equiv.symm i), ?_, ?_⟩
  · unfold IsKrausFamily
    have hs : ∑ i, (A (equiv.symm i))ᴴ * A (equiv.symm i) = ∑ k, (A k)ᴴ * A k :=
      equiv.symm.sum_comp (fun k => (A k)ᴴ * A k)
    exact hs.trans (h.2 hPOVM)
  · intro X
    change Entanglement.holevoMap R F X = ∑ i, A (equiv.symm i) * X * (A (equiv.symm i))ᴴ
    trans ∑ k, A k * X * (A k)ᴴ
    · exact (h.1 X).symm
    · exact (equiv.symm.sum_comp (fun k => A k * X * (A k)ᴴ)).symm

theorem solution (d m : ℕ) (hd : 0 < d)
    (R F : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef) :
    Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) ∧
      (IsPOVM F → IsChannel (Entanglement.holevoMap R F) ∧
        ∀ (a : ℕ) (ha : 0 < a),
          letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
          letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
          ∀ Gamma : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ,
            IsDensityMatrix Gamma →
              Entanglement.IsSeparableDensity
                (idTensorSuperop (Entanglement.holevoMap R F) Gamma)) := by
  have heb : Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) := by
    intro a ha X hX
    rcases output_decomposition ha R F hR hF X hX.1 with ⟨w, B, hw, hB, heq⟩
    exact ⟨m, w, B, R, hw, hB, heq⟩
  refine ⟨heb, fun hPOVM => ⟨holevo_channel hd R F hR hF hPOVM, ?_⟩⟩
  intro a ha
  letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro X hX
  exact separable_density_of_trace_one _ (heb a ha X hX)
    ((output_trace R F hR hPOVM X).trans hX.2)

#print axioms solution
