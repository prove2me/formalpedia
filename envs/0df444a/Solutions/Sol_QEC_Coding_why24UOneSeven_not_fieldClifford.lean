-- Prove2me | solution 1 for QEC.Coding.why24UOneSeven_not_fieldClifford
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:58.254089+00:00
-- url     : https://prove2.me/submissions/931ded88-fc1e-4b94-9dae-dac1e52d7461

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_adjoint
import Theorems.Thm_QEC_Coding_why24U_conjX_five
import Theorems.Thm_QEC_Coding_why24QuditZ_mul
import Theorems.Thm_QEC_Coding_why24UOneSeven_conjX_one
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_traceDual
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Coding.why24U_apply
section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24_binaryPhaseScalar_mul_self (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add, CharTwo.add_self_eq_zero,
    PauliSymplectic.binaryPhaseScalar_zero]
private theorem why24QuditX_isSymmetric (β : F1024) :
    (why24QuditX β).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, why24QuditX_apply, RCLike.inner_apply']
  exact Fintype.sum_equiv (Equiv.addRight β)
    (fun η => star (x (η + β)) * y η)
    (fun η => star (x η) * y (η + β)) (by
      intro η
      change star (x (η + β)) * y η =
        star (x (η + β)) * y ((η + β) + β)
      rw [show (η + β) + β = η by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]])
private theorem why24QuditX_adjoint (β : F1024) :
    LinearMap.adjoint (why24QuditX β) = why24QuditX β :=
  (why24QuditX_isSymmetric β).adjoint_eq
private theorem why24QuditZ_eq_u_one (γ : F1024) :
    why24QuditZ γ = why24U γ 1 := by
  ext ψ η
  simp [why24QuditZ_apply, why24U_apply]
private theorem why24QuditZ_adjoint (γ : F1024) :
    LinearMap.adjoint (why24QuditZ γ) = why24QuditZ γ := by
  rw [why24QuditZ_eq_u_one, why24U_adjoint]
private theorem why24QuditX_mul (β γ : F1024) :
    why24QuditX β * why24QuditX γ = why24QuditX (β + γ) := by
  ext ψ η
  simp only [Module.End.mul_apply, why24QuditX_apply]
  rw [add_assoc]
private theorem why24QuditZ_mul_qX (c b : F1024) :
    why24QuditZ c * why24QuditX b =
      PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (c * b)) •
        (why24QuditX b * why24QuditZ c) := by
  ext ψ η
  simp only [Module.End.mul_apply, why24QuditZ_apply, why24QuditX_apply,
    LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← PauliSymplectic.binaryPhaseScalar_add]
  congr 2
  rw [show c * (η + b) = c * η + c * b by ring, map_add]
  let u : ZMod 2 := Algebra.trace (ZMod 2) F1024 (c * η)
  let v : ZMod 2 := Algebra.trace (ZMod 2) F1024 (c * b)
  change u = v + (u + v)
  calc
    u = 0 + u := (zero_add u).symm
    _ = (v + v) + u := by rw [CharTwo.add_self_eq_zero]
    _ = v + (u + v) := by ac_rfl
private theorem why24PauliPhase_add (a b : ZMod 4) :
    why24PauliPhase (a + b) = why24PauliPhase a * why24PauliPhase b := by
  fin_cases a <;> fin_cases b
  · change Complex.I ^ 0 = Complex.I ^ 0 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 0 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 0 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 0 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 1 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 1 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 1 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 1 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 2 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 2 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 2 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 2 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 3 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 3 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 3 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 3 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
private theorem why24PauliPhase_star (a : ZMod 4) :
    star (why24PauliPhase a) = why24PauliPhase (-a) := by
  fin_cases a
  · change star (Complex.I ^ 0) = Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 1) = Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 2) = Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 3) = Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
private theorem why24PauliPhase_two_trace (t : ZMod 2) :
    why24PauliPhase (2 * (t.val : ZMod 4)) =
      PauliSymplectic.binaryPhaseScalar t := by
  fin_cases t
  · change Complex.I ^ 0 = (1 : Complex)
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = (-1 : Complex)
    norm_num [pow_succ, Complex.I_sq]
private theorem why24FieldPauliOperator_X (β : F1024) :
    why24FieldPauliOperator (0, β, 0) = why24QuditX β := by
  ext ψ η
  simp [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
    why24QuditX_apply, why24QuditZ_apply, smul_eq_mul]
private theorem why24FieldPauliOperator_Z (γ : F1024) :
    why24FieldPauliOperator (0, 0, γ) = why24QuditZ γ := by
  ext ψ η
  simp [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
    why24QuditX_apply, why24QuditZ_apply, smul_eq_mul]
private theorem why24QuditXZ_mul (b c e f : F1024) :
    (why24QuditX b * why24QuditZ c) * (why24QuditX e * why24QuditZ f) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        (why24QuditX (b + e) * why24QuditZ (c + f)) := by
  calc
    (why24QuditX b * why24QuditZ c) *
        (why24QuditX e * why24QuditZ f) =
        why24QuditX b * (why24QuditZ c * why24QuditX e) * why24QuditZ f := by
          simp only [mul_assoc]
    _ = why24QuditX b *
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (c * e)) •
          (why24QuditX e * why24QuditZ c)) * why24QuditZ f := by
          rw [why24QuditZ_mul_qX]
    _ = PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        ((why24QuditX b * why24QuditX e) *
          (why24QuditZ c * why24QuditZ f)) := by
          rw [mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
    _ = PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        (why24QuditX (b + e) * why24QuditZ (c + f)) := by
          rw [why24QuditX_mul, why24QuditZ_mul]
private theorem why24FieldPauliOperator_mul (P Q : Why24FieldPauli) :
    why24FieldPauliOperator (why24FieldPauliMul P Q) =
      why24FieldPauliOperator P * why24FieldPauliOperator Q := by
  rcases P with ⟨a, b, c⟩
  rcases Q with ⟨d, e, f⟩
  change why24PauliPhase
      (a + d + 2 * ((Algebra.trace (ZMod 2) F1024 (c * e)).val : ZMod 4)) •
      (why24QuditX (b + e) * why24QuditZ (c + f)) =
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        (why24PauliPhase d • (why24QuditX e * why24QuditZ f))
  rw [show
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        (why24PauliPhase d • (why24QuditX e * why24QuditZ f)) =
        (why24PauliPhase a * why24PauliPhase d) •
          ((why24QuditX b * why24QuditZ c) *
            (why24QuditX e * why24QuditZ f)) by
      rw [smul_mul_smul_comm], why24QuditXZ_mul, smul_smul,
    ← why24PauliPhase_two_trace, ← why24PauliPhase_add,
    ← why24PauliPhase_add]
private theorem why24FieldPauliOperator_adjoint (P : Why24FieldPauli) :
    why24FieldPauliOperator (why24FieldPauliDagger P) =
      LinearMap.adjoint (why24FieldPauliOperator P) := by
  rcases P with ⟨a, b, c⟩
  change why24PauliPhase
      (-a + 2 * ((Algebra.trace (ZMod 2) F1024 (b * c)).val : ZMod 4)) •
      (why24QuditX b * why24QuditZ c) =
        LinearMap.adjoint
          (why24PauliPhase a • (why24QuditX b * why24QuditZ c))
  rw [show LinearMap.adjoint
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
      star (why24PauliPhase a) •
        (why24QuditZ c * why24QuditX b) by
      calc
        LinearMap.adjoint
            (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
            star (why24PauliPhase a) •
              LinearMap.adjoint (why24QuditX b * why24QuditZ c) := by
                exact map_smulₛₗ
                  (LinearMap.adjoint :
                    Semantics.Operator Why24QuditSpace ≃ₗ⋆[Complex]
                      Semantics.Operator Why24QuditSpace)
                  (why24PauliPhase a) (why24QuditX b * why24QuditZ c)
        _ = star (why24PauliPhase a) •
            (why24QuditZ c * why24QuditX b) := by
              rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
                ← Module.End.mul_eq_comp, why24QuditX_adjoint,
                why24QuditZ_adjoint]]
  rw [why24QuditZ_mul_qX, smul_smul, why24PauliPhase_star,
    ← why24PauliPhase_two_trace, ← why24PauliPhase_add]
  ring_nf
private theorem why24Alpha_pow_eq_mk (k : ℕ) :
    f1024Alpha ^ k = AdjoinRoot.mk f1024Modulus (Polynomial.X ^ k) := by
  simp [f1024Alpha, ← AdjoinRoot.mk_X]
private theorem why24_square_residue (p r q : Polynomial (ZMod 2))
    (h : p ^ 2 = f1024Modulus * q + r) :
    (AdjoinRoot.mk f1024Modulus p) ^ 2 = AdjoinRoot.mk f1024Modulus r := by
  rw [← (AdjoinRoot.mk f1024Modulus).map_pow, h, map_add, map_mul,
    AdjoinRoot.mk_self, zero_mul, zero_add]
private theorem why24FrobeniusRootFour_alpha :
    why24FrobeniusRootFour f1024Alpha =
      AdjoinRoot.mk f1024Modulus
        (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
  have h0 : f1024Alpha ^ 16 =
      AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6) := by
    calc
      f1024Alpha ^ 16 = (f1024Alpha ^ 8) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 8)) ^ 2 := by
        rw [why24Alpha_pow_eq_mk]
      _ = AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6) := by
        apply why24_square_residue (Polynomial.X ^ 8)
          (Polynomial.X ^ 9 + Polynomial.X ^ 6) (Polynomial.X ^ 6)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h1 : f1024Alpha ^ 32 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X) := by
    calc
      f1024Alpha ^ 32 = (f1024Alpha ^ 16) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6)) ^ 2 := by rw [h0]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X) := by
        apply why24_square_residue (Polynomial.X ^ 9 + Polynomial.X ^ 6)
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 8 + Polynomial.X ^ 2 + Polynomial.X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h2 : f1024Alpha ^ 64 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
        Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) := by
    calc
      f1024Alpha ^ 64 = (f1024Alpha ^ 32) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)) ^ 2 := by rw [h1]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) := by
        apply why24_square_residue
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) (Polynomial.X ^ 6 + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h3 : f1024Alpha ^ 128 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1) := by
    calc
      f1024Alpha ^ 128 = (f1024Alpha ^ 64) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1)) ^ 2 := by rw [h2]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1) := by
        apply why24_square_residue
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1)
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)
          (Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 2 + Polynomial.X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h4 : f1024Alpha ^ 256 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
    calc
      f1024Alpha ^ 256 = (f1024Alpha ^ 128) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)) ^ 2 := by rw [h3]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
        apply why24_square_residue
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)
          (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 8 + Polynomial.X + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  exact h4
private theorem why24_rootFour_alpha_add_alpha_pow_four_ne_zero :
    why24FrobeniusRootFour f1024Alpha + f1024Alpha ^ 4 ≠ 0 := by
  rw [why24FrobeniusRootFour_alpha, why24Alpha_pow_eq_mk]
  simp only [map_add, map_pow, AdjoinRoot.mk_X]
  intro hzero
  have hdiv : f1024Modulus ∣
      Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 :=
    AdjoinRoot.mk_eq_zero.mp hzero
  have hpoly_ne :
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun f : Polynomial (ZMod 2) => f.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at hcoeff
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv hpoly_ne
  have htarget_degree :
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 : Polynomial (ZMod 2)).natDegree ≤ 8 := by
    apply Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_add_le_of_degree_le
          (Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)) (by simp))
        (by simp))
      (by simp)
  rw [f1024Modulus_natDegree] at hdegree
  omega
private theorem exists_why24_trace_mul_ne_zero {d : F1024} (hd : d ≠ 0) :
    ∃ η : F1024, Algebra.trace (ZMod 2) F1024 (d * η) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hd
  apply f1024SelectedCoordinates.injective
  funext i
  have hcoordinate :
      Algebra.trace (ZMod 2) F1024 (d * f1024SelectedSelfDualBasis i) =
        f1024SelectedCoordinates d i := by
    calc
      Algebra.trace (ZMod 2) F1024 (d * f1024SelectedSelfDualBasis i) =
          (f1024SelectedSelfDualBasis.traceDual).repr d i := by
            simpa only [Algebra.traceForm_apply] using
              (Module.Basis.traceDual_repr_apply f1024SelectedSelfDualBasis d i).symm
      _ = f1024SelectedSelfDualBasis.repr d i := by
            rw [f1024SelectedSelfDualBasis_traceDual]
      _ = f1024SelectedCoordinates d i := rfl
  simpa using hcoordinate.symm.trans (h (f1024SelectedSelfDualBasis i))
private theorem why24QuditX_zero : why24QuditX (0 : F1024) = 1 := by
  ext ψ η
  simp [why24QuditX_apply]
private theorem why24QuditZ_zero : why24QuditZ (0 : F1024) = 1 := by
  ext ψ η
  simp [why24QuditZ_apply]
private theorem why24QuditX_mul_self (b : F1024) :
    why24QuditX b * why24QuditX b = 1 := by
  rw [why24QuditX_mul, CharTwo.add_self_eq_zero, why24QuditX_zero]
private theorem why24QuditZ_mul_self (c : F1024) :
    why24QuditZ c * why24QuditZ c = 1 := by
  rw [why24QuditZ_mul, CharTwo.add_self_eq_zero, why24QuditZ_zero]
private theorem why24FieldPauliOperator_conjX (P : Why24FieldPauli) (γ : F1024) :
    ∃ a : ZMod 4,
      why24FieldPauliOperator P * why24QuditX γ *
        LinearMap.adjoint (why24FieldPauliOperator P) =
          why24FieldPauliOperator (a, γ, 0) := by
  rcases P with ⟨a, b, c⟩
  let Xlabel : Why24FieldPauli := (0, γ, 0)
  let R : Why24FieldPauli :=
    why24FieldPauliMul
      (why24FieldPauliMul (a, b, c) Xlabel)
      (why24FieldPauliDagger (a, b, c))
  have hX : why24QuditX γ = why24FieldPauliOperator Xlabel := by
    simpa [Xlabel] using (why24FieldPauliOperator_X γ).symm
  have hR :
      why24FieldPauliOperator (a, b, c) * why24FieldPauliOperator Xlabel *
        LinearMap.adjoint (why24FieldPauliOperator (a, b, c)) =
          why24FieldPauliOperator R := by
    simp only [R]
    rw [why24FieldPauliOperator_mul, why24FieldPauliOperator_mul,
      why24FieldPauliOperator_adjoint]
  have hlabel : b + γ + b = γ := by
    calc
      b + γ + b = γ + (b + b) := by ac_rfl
      _ = γ := by rw [CharTwo.add_self_eq_zero, add_zero]
  refine ⟨R.1, ?_⟩
  rw [hX]
  calc
    why24FieldPauliOperator (a, b, c) * why24FieldPauliOperator Xlabel *
        LinearMap.adjoint (why24FieldPauliOperator (a, b, c)) =
        why24FieldPauliOperator R := hR
    _ = why24FieldPauliOperator (R.1, γ, 0) := by
      congr 1
      simp [R, Xlabel, why24FieldPauliMul, why24FieldPauliDagger,
        CharTwo.add_self_eq_zero, hlabel]
private theorem why24U_five_not_fieldPauli :
    ¬ ∃ P : Why24FieldPauli, why24U (1 : F1024) 5 = why24FieldPauliOperator P := by
  intro hpauli
  rcases hpauli with ⟨P, hP⟩
  let d : F1024 := why24FrobeniusRootFour f1024Alpha + f1024Alpha ^ 4
  have hd : d ≠ 0 := by
    simpa [d] using why24_rootFour_alpha_add_alpha_pow_four_ne_zero
  obtain ⟨η, hη⟩ := exists_why24_trace_mul_ne_zero hd
  obtain ⟨a, ha⟩ := why24FieldPauliOperator_conjX P f1024Alpha
  have hconj := why24U_conjX_five (1 : F1024) f1024Alpha
  rw [hP] at hconj
  have heq : why24FieldPauliOperator (a, f1024Alpha, 0) =
      PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) •
        (why24QuditX f1024Alpha * why24QuditZ d) := by
    calc
      why24FieldPauliOperator (a, f1024Alpha, 0) =
          why24FieldPauliOperator P * why24QuditX f1024Alpha *
            LinearMap.adjoint (why24FieldPauliOperator P) := ha.symm
      _ = PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) •
          (why24QuditX f1024Alpha * why24QuditZ d) := by
            simpa [d, mul_assoc] using hconj
  have hbase := congrArg
    (fun T : Semantics.Operator Why24QuditSpace =>
      T (why24QuditComputationalBasis (0 : F1024)) f1024Alpha) heq
  have hshift : (η + f1024Alpha) + f1024Alpha = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hpoint := congrArg
    (fun T : Semantics.Operator Why24QuditSpace =>
      T (why24QuditComputationalBasis η) (η + f1024Alpha)) heq
  have hbase' : why24PauliPhase a =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) := by
    simpa [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
      why24QuditX_apply, why24QuditZ_apply, why24QuditComputationalBasis,
      PiLp.single_apply, smul_eq_mul, CharTwo.add_self_eq_zero] using hbase
  have hpoint' : why24PauliPhase a =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) *
        PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (d * η)) := by
    simpa [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
      why24QuditX_apply, why24QuditZ_apply, why24QuditComputationalBasis,
      PiLp.single_apply, smul_eq_mul, hshift] using hpoint
  let s : Complex := PauliSymplectic.binaryPhaseScalar
    (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5))
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    by_cases ht : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 5) = 0
    · simp [PauliSymplectic.binaryPhaseScalar, ht]
    · have htRaw :
        Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5) ≠ 0 := by
          simpa only [one_mul] using ht
      rw [PauliSymplectic.zmod_two_eq_one_of_ne_zero htRaw]
      simp
  have hphase : PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (d * η)) = 1 := by
    apply mul_left_cancel₀ hs_ne
    simpa only [mul_one] using hpoint'.symm.trans hbase'
  apply hη
  exact (PauliSymplectic.binaryPhaseScalar_eq_one_iff _).mp hphase
private theorem why24U_five_is_fieldPauli_of_u7_normalizes
    (hU : why24FieldNormalizesPaulis why24UOneSeven) :
    ∃ P : Why24FieldPauli, why24U (1 : F1024) 5 = why24FieldPauliOperator P := by
  let t : ZMod 2 := Algebra.trace (ZMod 2) F1024 ((1 : F1024) ^ 7)
  let Xlabel : Why24FieldPauli := (0, (1 : F1024), 0)
  obtain ⟨Q, hQ⟩ := hU Xlabel
  have hX : why24FieldPauliOperator Xlabel = why24QuditX (1 : F1024) := by
    simpa [Xlabel] using why24FieldPauliOperator_X (1 : F1024)
  have hconj : PauliSymplectic.binaryPhaseScalar t •
      (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 * why24QuditZ (1 : F1024)) =
        why24FieldPauliOperator Q := by
    calc
      PauliSymplectic.binaryPhaseScalar t •
          (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
            why24QuditZ (1 : F1024)) =
          why24UOneSeven * why24QuditX (1 : F1024) *
            LinearMap.adjoint why24UOneSeven := by
              simpa [t] using why24UOneSeven_conjX_one.symm
      _ = why24FieldPauliOperator Q := by simpa [hX] using hQ
  have hsign : why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
      why24QuditZ (1 : F1024) =
        PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator Q := by
    calc
      why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
          why24QuditZ (1 : F1024) =
          (1 : Complex) •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024)) := by simp
      _ = (PauliSymplectic.binaryPhaseScalar t *
          PauliSymplectic.binaryPhaseScalar t) •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024)) := by
                rw [why24_binaryPhaseScalar_mul_self]
      _ = PauliSymplectic.binaryPhaseScalar t •
          (PauliSymplectic.binaryPhaseScalar t •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024))) := by rw [smul_smul]
      _ = PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator Q := by
            rw [hconj]
  rcases Q with ⟨a, b, c⟩
  let phaseLabel : Why24FieldPauli := (a + 2 * (t.val : ZMod 4), b, c)
  have hphase : PauliSymplectic.binaryPhaseScalar t •
      why24FieldPauliOperator (a, b, c) = why24FieldPauliOperator phaseLabel := by
    change PauliSymplectic.binaryPhaseScalar t •
        (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
      why24PauliPhase (a + 2 * (t.val : ZMod 4)) •
        (why24QuditX b * why24QuditZ c)
    rw [smul_smul, ← why24PauliPhase_two_trace,
      mul_comm (why24PauliPhase (2 * (t.val : ZMod 4))) (why24PauliPhase a),
      ← why24PauliPhase_add]
  let Zlabel : Why24FieldPauli := (0, 0, (1 : F1024))
  refine ⟨why24FieldPauliMul
      (why24FieldPauliMul Xlabel phaseLabel) Zlabel, ?_⟩
  calc
    why24U (1 : F1024) 5 =
        (1 : Semantics.Operator Why24QuditSpace) * why24U (1 : F1024) 5 *
          (1 : Semantics.Operator Why24QuditSpace) := by simp
    _ = (why24QuditX (1 : F1024) * why24QuditX (1 : F1024)) *
        why24U (1 : F1024) 5 *
        (why24QuditZ (1 : F1024) * why24QuditZ (1 : F1024)) := by
          rw [why24QuditX_mul_self, why24QuditZ_mul_self]
    _ = why24QuditX (1 : F1024) *
        (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
          why24QuditZ (1 : F1024)) * why24QuditZ (1 : F1024) := by
          simp only [mul_assoc]
    _ = why24QuditX (1 : F1024) *
        (PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator (a, b, c)) *
          why24QuditZ (1 : F1024) := by rw [hsign]
    _ = why24QuditX (1 : F1024) * why24FieldPauliOperator phaseLabel *
          why24QuditZ (1 : F1024) := by rw [hphase]
    _ = why24FieldPauliOperator
        (why24FieldPauliMul (why24FieldPauliMul Xlabel phaseLabel) Zlabel) := by
            rw [← hX, ← why24FieldPauliOperator_Z]
            simp only [Zlabel]
            rw [← why24FieldPauliOperator_mul, ← why24FieldPauliOperator_mul]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution : ¬ Why24FieldClifford why24UOneSeven := by
  intro hclifford
  apply why24U_five_not_fieldPauli
  exact why24U_five_is_fieldPauli_of_u7_normalizes hclifford.2
end QEC.Coding
