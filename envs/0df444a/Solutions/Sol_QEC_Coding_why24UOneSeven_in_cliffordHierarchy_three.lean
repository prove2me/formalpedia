-- Prove2me | solution 1 for QEC.Coding.why24UOneSeven_in_cliffordHierarchy_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:49.395513+00:00
-- url     : https://prove2.me/submissions/4b094a4e-ed9c-478e-9b16-dcee5da99c86

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_adjoint
import Theorems.Thm_QEC_Coding_why24U_isUnitary
import Theorems.Thm_QEC_Coding_why24FrobeniusRootTwo_sq
import Theorems.Thm_QEC_Coding_why24FrobeniusRootFour_pow_four
import Theorems.Thm_QEC_Coding_why24_trace_sq
import Theorems.Thm_QEC_Coding_why24U_conjX_five
import Theorems.Thm_QEC_Coding_why24QuditZ_mul
import Theorems.Thm_QEC_Coding_why24U_mul_qZ
import Theorems.Thm_QEC_Coding_why24U_fieldClifford_three
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
private theorem why24_trace_eq_of_sq {x y : F1024} (hxy : x ^ 2 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  rw [← why24_trace_sq x, hxy]
private theorem why24_trace_eq_of_pow_four {x y : F1024} (hxy : x ^ 4 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  calc
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 (x ^ 2) :=
      (why24_trace_sq x).symm
    _ = Algebra.trace (ZMod 2) F1024 ((x ^ 2) ^ 2) :=
      (why24_trace_sq (x ^ 2)).symm
    _ = Algebra.trace (ZMod 2) F1024 (x ^ 4) := by ring_nf
    _ = Algebra.trace (ZMod 2) F1024 y := by rw [hxy]
private theorem why24PauliPhase_add_two_mul (a : ZMod 4) (t : ZMod 2) :
    why24PauliPhase (a + 2 * (t.val : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar t := by
  fin_cases t
  · change why24PauliPhase (a + 2 * (0 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 0
    simp [why24PauliPhase]
  · change why24PauliPhase (a + 2 * (1 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 1
    rw [PauliSymplectic.binaryPhaseScalar_one]
    fin_cases a
    · change Complex.I ^ 2 = Complex.I ^ 0 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 3 = Complex.I ^ 1 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 0 = Complex.I ^ 2 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 1 = Complex.I ^ 3 * (-1)
      norm_num [pow_succ, Complex.I_sq]
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
private theorem why24FieldPauliOperator_phase (a : ZMod 4) :
    why24FieldPauliOperator (a, 0, 0) =
      why24PauliPhase a • (1 : Semantics.Operator Why24QuditSpace) := by
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
private theorem why24FieldPauliOperator_conj (P Q : Why24FieldPauli) :
    ∃ R : Why24FieldPauli,
      why24FieldPauliOperator P * why24FieldPauliOperator Q *
        LinearMap.adjoint (why24FieldPauliOperator P) = why24FieldPauliOperator R := by
  refine ⟨why24FieldPauliMul (why24FieldPauliMul P Q) (why24FieldPauliDagger P), ?_⟩
  rw [why24FieldPauliOperator_mul, why24FieldPauliOperator_mul,
    why24FieldPauliOperator_adjoint]
private theorem why24U_conjPauli_five (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 5 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 5) =
      why24FieldPauliOperator
        (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4), b,
          why24FrobeniusRootFour (β * b) + β * b ^ 4 + c) := by
  change why24U β 5 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 5) = _
  rw [show why24U β 5 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 5) = why24PauliPhase a •
        (why24U β 5 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 5)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 5 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 5) =
      LinearMap.adjoint (why24U β 5) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 5 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 5) =
      (why24U β 5 * why24QuditX b * LinearMap.adjoint (why24U β 5)) *
        why24QuditZ c by
        calc
          why24U β 5 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 5) =
              (why24U β 5 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 5)) := by
                rw [mul_assoc]
          _ = (why24U β 5 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 5) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 5 * why24QuditX b * LinearMap.adjoint (why24U β 5)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_five]
  rw [smul_mul_assoc]
  rw [show (why24QuditX b *
      why24QuditZ (why24FrobeniusRootFour (β * b) + β * b ^ 4)) * why24QuditZ c =
      why24QuditX b *
        why24QuditZ (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c) by
      rw [mul_assoc, why24QuditZ_mul]]
  change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * b ^ 5)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c))) =
    why24PauliPhase
      (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c))
  rw [why24PauliPhase_add_two_mul, mul_smul]
private theorem why24U_fieldClifford_five (β : F1024) : Why24FieldClifford (why24U β 5) := by
  constructor
  · exact why24U_isUnitary β 5
  · rintro ⟨a, b, c⟩
    refine ⟨(a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4), b,
      why24FrobeniusRootFour (β * b) + β * b ^ 4 + c), ?_⟩
    exact why24U_conjPauli_five β a b c
private theorem why24InCliffordHierarchy_two_of_normalizes
    {C : Semantics.Operator Why24QuditSpace}
    (hC : why24FieldNormalizesPaulis C) : why24InCliffordHierarchy 2 C := by
  intro P
  obtain ⟨Q, hQ⟩ := hC P
  exact ⟨why24FieldPauliOperator Q, ⟨Q, rfl⟩, hQ⟩
private theorem why24FieldPauli_inCliffordHierarchy_two (P : Why24FieldPauli) :
    why24InCliffordHierarchy 2 (why24FieldPauliOperator P) := by
  intro Q
  obtain ⟨R, hR⟩ := why24FieldPauliOperator_conj P Q
  exact ⟨why24FieldPauliOperator R, ⟨R, rfl⟩, hR⟩
private theorem why24InCliffordHierarchy_two_mul
    {A B : Semantics.Operator Why24QuditSpace}
    (hA : why24InCliffordHierarchy 2 A)
    (hB : why24InCliffordHierarchy 2 B) :
    why24InCliffordHierarchy 2 (A * B) := by
  intro P
  obtain ⟨Q, ⟨q, hQ⟩, hBQ⟩ := hB P
  obtain ⟨R, hR, hAR⟩ := hA q
  refine ⟨R, hR, ?_⟩
  rw [show LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A by
      rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]]
  calc
    A * B * why24FieldPauliOperator P *
        (LinearMap.adjoint B * LinearMap.adjoint A) =
        A * (B * why24FieldPauliOperator P * LinearMap.adjoint B) *
          LinearMap.adjoint A := by
            simp only [mul_assoc]
    _ = A * Q * LinearMap.adjoint A := by rw [hBQ]
    _ = A * why24FieldPauliOperator q * LinearMap.adjoint A := by rw [hQ]
    _ = R := hAR
private theorem why24U_three_inCliffordHierarchy_two (β : F1024) :
    why24InCliffordHierarchy 2 (why24U β 3) :=
  why24InCliffordHierarchy_two_of_normalizes (why24U_fieldClifford_three β).2
private theorem why24U_five_inCliffordHierarchy_two (β : F1024) :
    why24InCliffordHierarchy 2 (why24U β 5) :=
  why24InCliffordHierarchy_two_of_normalizes (why24U_fieldClifford_five β).2
private theorem why24_trace_u_seven_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3) +
          Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * η ^ 5) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η) := by
  have hsix : (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 = β * γ * η ^ 6 := by
    calc
      (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 =
          why24FrobeniusRootTwo (β * γ) ^ 2 * (η ^ 3) ^ 2 := by rw [mul_pow]
      _ = β * γ * η ^ 6 := by rw [why24FrobeniusRootTwo_sq]; ring
  have hfour : (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
      β * γ ^ 3 * η ^ 4 := by
    calc
      (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
          why24FrobeniusRootFour (β * γ ^ 3) ^ 4 * η ^ 4 := by rw [mul_pow]
      _ = β * γ ^ 3 * η ^ 4 := by rw [why24FrobeniusRootFour_pow_four]
  have htwo : (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
      β * γ ^ 5 * η ^ 2 := by
    calc
      (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
          why24FrobeniusRootTwo (β * γ ^ 5) ^ 2 * η ^ 2 := by rw [mul_pow]
      _ = β * γ ^ 5 * η ^ 2 := by rw [why24FrobeniusRootTwo_sq]
  have hrootSix :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ) * η ^ 3) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6) :=
    why24_trace_eq_of_sq hsix
  have hrootFour :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootFour (β * γ ^ 3) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4) :=
    why24_trace_eq_of_pow_four hfour
  have hrootTwo :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ ^ 5) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2) :=
    why24_trace_eq_of_sq htwo
  have htwoChar : (2 : F1024) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hthree : (3 : F1024) = 1 := by
    calc
      (3 : F1024) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hfive : (5 : F1024) = 1 := by
    calc
      (5 : F1024) = 2 * 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hseven : (7 : F1024) = 1 := by
    calc
      (7 : F1024) = 2 * 3 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have htwentyOne : (21 : F1024) = 1 := by
    calc
      (21 : F1024) = 2 * 10 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hthirtyFive : (35 : F1024) = 1 := by
    calc
      (35 : F1024) = 2 * 17 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hbinomial : β * (η + γ) ^ 7 =
      β * η ^ 7 + β * γ ^ 7 + β * γ * η ^ 6 + β * γ ^ 2 * η ^ 5 +
        β * γ ^ 3 * η ^ 4 + β * γ ^ 4 * η ^ 3 + β * γ ^ 5 * η ^ 2 +
          β * γ ^ 6 * η := by
    ring_nf
    rw [hseven, htwentyOne, hthirtyFive]
    ring
  rw [hbinomial]
  repeat' rw [map_add]
  rw [show (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3 =
      why24FrobeniusRootTwo (β * γ) * η ^ 3 + β * γ ^ 4 * η ^ 3 by ring,
    show (why24FrobeniusRootFour (β * γ ^ 3) +
        why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η =
      why24FrobeniusRootFour (β * γ ^ 3) * η +
        why24FrobeniusRootTwo (β * γ ^ 5) * η + β * γ ^ 6 * η by ring]
  repeat' rw [map_add]
  rw [hrootSix, hrootFour, hrootTwo]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 7)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 2 * η ^ 5)
  let e : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4)
  let f : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 4 * η ^ 3)
  let g : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2)
  let h : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 6 * η)
  change a + (a + b + c + d + e + f + g + h) = b + (c + f) + d + (e + g + h)
  calc
    a + (a + b + c + d + e + f + g + h) =
        (a + a) + b + c + d + e + f + g + h := by ac_rfl
    _ = b + (c + f) + d + (e + g + h) := by
      rw [CharTwo.add_self_eq_zero]
      ac_rfl
private theorem why24U_conjX_seven (β γ : F1024) :
    why24U β 7 * why24QuditX γ * LinearMap.adjoint (why24U β 7) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) •
        (why24QuditX γ *
          why24U (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) 3 *
          why24U (β * γ ^ 2) 5 *
          why24QuditZ
            (why24FrobeniusRootFour (β * γ ^ 3) +
              why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply, why24QuditZ_apply,
    smul_eq_mul]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3)) *
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5)) *
          (PauliSymplectic.binaryPhaseScalar
            (Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ))) *
            ψ (η + γ))))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  repeat' rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_seven_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3) +
            Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                  why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']
private theorem why24QuditX_inCliffordHierarchy_two (γ : F1024) :
    why24InCliffordHierarchy 2 (why24QuditX γ) := by
  rw [← why24FieldPauliOperator_X]
  exact why24FieldPauli_inCliffordHierarchy_two _
private theorem why24QuditZ_inCliffordHierarchy_two (γ : F1024) :
    why24InCliffordHierarchy 2 (why24QuditZ γ) := by
  rw [← why24FieldPauliOperator_Z]
  exact why24FieldPauli_inCliffordHierarchy_two _
private theorem why24U_conjPauli_seven (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 7 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 7) =
      why24PauliPhase a •
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (β * b ^ 7)) •
          (why24QuditX b *
            why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
            why24U (β * b ^ 2) 5 *
            why24QuditZ
              (why24FrobeniusRootFour (β * b ^ 3) +
                why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c))) := by
  change why24U β 7 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 7) = _
  rw [show why24U β 7 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 7) = why24PauliPhase a •
        (why24U β 7 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 7)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 7 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 7) =
      LinearMap.adjoint (why24U β 7) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 7 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 7) =
      (why24U β 7 * why24QuditX b * LinearMap.adjoint (why24U β 7)) *
        why24QuditZ c by
        calc
          why24U β 7 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 7) =
              (why24U β 7 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 7)) := by
                rw [mul_assoc]
          _ = (why24U β 7 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 7) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 7 * why24QuditX b * LinearMap.adjoint (why24U β 7)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_seven]
  rw [smul_mul_assoc]
  have hZ :
      (why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6)) * why24QuditZ c =
      why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c) := by
    calc
      (why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6)) * why24QuditZ c =
        why24QuditX b *
          why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
          why24U (β * b ^ 2) 5 *
          (why24QuditZ
            (why24FrobeniusRootFour (β * b ^ 3) +
              why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6) * why24QuditZ c) := by
            simp only [mul_assoc]
      _ = why24QuditX b *
          why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
          why24U (β * b ^ 2) 5 *
          why24QuditZ
            (why24FrobeniusRootFour (β * b ^ 3) +
              why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c) := by
            rw [why24QuditZ_mul]
  rw [hZ]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution :
    why24InCliffordHierarchy 3 why24UOneSeven := by
  intro P
  rcases P with ⟨a, b, c⟩
  let traceBit : ZMod 2 := Algebra.trace (ZMod 2) F1024 ((1 : F1024) * b ^ 7)
  let A : F1024 := why24FrobeniusRootTwo ((1 : F1024) * b) + (1 : F1024) * b ^ 4
  let B : F1024 := (1 : F1024) * b ^ 2
  let C : F1024 := why24FrobeniusRootFour ((1 : F1024) * b ^ 3) +
    why24FrobeniusRootTwo ((1 : F1024) * b ^ 5) + (1 : F1024) * b ^ 6 + c
  refine ⟨why24FieldPauliOperator
      (a + 2 * (traceBit.val : ZMod 4), 0, 0) *
        why24QuditX b * why24U A 3 * why24U B 5 * why24QuditZ C, ?_, ?_⟩
  · apply why24InCliffordHierarchy_two_mul
    · apply why24InCliffordHierarchy_two_mul
      · apply why24InCliffordHierarchy_two_mul
        · apply why24InCliffordHierarchy_two_mul
          · exact why24FieldPauli_inCliffordHierarchy_two _
          · exact why24QuditX_inCliffordHierarchy_two b
        · exact why24U_three_inCliffordHierarchy_two A
      · exact why24U_five_inCliffordHierarchy_two B
    · exact why24QuditZ_inCliffordHierarchy_two C
  · rw [why24U_conjPauli_seven]
    change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar traceBit •
        (why24QuditX b * why24U A 3 * why24U B 5 * why24QuditZ C)) = _
    rw [why24FieldPauliOperator_phase]
    rw [why24PauliPhase_add, why24PauliPhase_two_trace]
    simp only [smul_mul_assoc, smul_smul, one_mul]
end QEC.Coding
