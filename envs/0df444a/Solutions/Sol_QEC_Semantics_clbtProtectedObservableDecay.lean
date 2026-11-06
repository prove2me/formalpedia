-- Prove2me | solution 1 for QEC.Semantics.clbtProtectedObservableDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:13:45.219949+00:00
-- url     : https://prove2.me/submissions/14c07600-ce70-440b-8245-b919793cb3cc

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolution_traceNorm_sub_le_time_mul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_commute_physicalGibbsState
import Theorems.Thm_QEC_Semantics_JumpProtected_one
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_JumpProtected_smul
import Theorems.Thm_QEC_Semantics_JumpProtected_mul_of_commute_projector
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_map_isSymmetric
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_encodedObservable_operatorNorm_le_two
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalGibbsState_eq_thermalReferenceState
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalDecoding_thermalEncoding_density
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_eq_encodedObservable_mul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_tensorMap_positive
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_clbtFourBlockGeneratorEstimate
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


section
universe u v
namespace QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
private theorem qubitOperator_eq_pauli_span (A : Operator Qubit.QubitSpace) :
    ∃ alpha gamma delta epsilon : ℂ,
      A = alpha • 1 + gamma • Qubit.pauliZ +
        delta • Qubit.pauliX + epsilon • (Qubit.pauliX * Qubit.pauliZ) := by
  let e0 : Qubit.QubitSpace := EuclideanSpace.basisFun (Fin 2) ℂ 0
  let e1 : Qubit.QubitSpace := EuclideanSpace.basisFun (Fin 2) ℂ 1
  refine ⟨(2 : ℂ)⁻¹ * (A e0 0 + A e1 1),
    (2 : ℂ)⁻¹ * (A e0 0 - A e1 1),
    (2 : ℂ)⁻¹ * (A e0 1 + A e1 0),
    (2 : ℂ)⁻¹ * (A e0 1 - A e1 0), ?_⟩
  apply LinearMap.ext
  intro psi
  have hpsi : psi = psi 0 • EuclideanSpace.basisFun (Fin 2) ℂ 0 +
      psi 1 • EuclideanSpace.basisFun (Fin 2) ℂ 1 := by
    ext i
    fin_cases i <;> simp
  rw [hpsi, map_add, map_smul, map_smul]
  ext i
  fin_cases i <;>
    simp [e0, e1, Module.End.mul_apply, Qubit.zPhase] <;>
    ring
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_eq_encodedObservable
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) :
    logical.liftQubitOperator ((2 : ℂ) • eta.toOperator) =
      logical.encodedObservable eta := by
  rfl
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_one
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator 1 = 1 := by
  simp [ThermalEncoding.PauliLikePair.liftQubitOperator]
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauliX
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator Qubit.pauliX = logical.x := by
  exact logical.conj_tensorPauliX
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauliZ
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K) :
    logical.liftQubitOperator Qubit.pauliZ = logical.z := by
  exact logical.conj_tensorPauliZ
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_add
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A B : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (A + B) =
      logical.liftQubitOperator A + logical.liftQubitOperator B := by
  change logical.factorization.conjOperator
      (TensorProduct.map (A + B) 1) = _
  rw [TensorProduct.map_add_left]
  exact map_add logical.factorization.conjOperatorLinearMap _ _
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_smul
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (c : ℂ) (A : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (c • A) =
      c • logical.liftQubitOperator A := by
  change logical.factorization.conjOperator
      (TensorProduct.map (c • A) 1) = _
  rw [TensorProduct.map_smul_left]
  exact map_smul logical.factorization.conjOperatorLinearMap _ _
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_mul
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A B : Operator Qubit.QubitSpace) :
    logical.liftQubitOperator (A * B) =
      logical.liftQubitOperator A * logical.liftQubitOperator B := by
  rw [ThermalEncoding.PauliLikePair.liftQubitOperator,
    ThermalEncoding.PauliLikePair.liftQubitOperator,
    ThermalEncoding.PauliLikePair.liftQubitOperator,
    ← logical.factorization.conjOperator_mul,
    ← TensorProduct.map_mul]
  simp
private theorem ThermalEncoding.PauliLikePair.liftQubitOperator_pauli_span
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) :
    ∃ alpha gamma delta epsilon : ℂ,
      logical.liftQubitOperator A =
        alpha • 1 + gamma • logical.z + delta • logical.x +
          epsilon • (logical.x * logical.z) := by
  rcases qubitOperator_eq_pauli_span A with ⟨alpha, gamma, delta, epsilon, hA⟩
  rw [hA]
  refine ⟨alpha, gamma, delta, epsilon, ?_⟩
  rw [logical.liftQubitOperator_add, logical.liftQubitOperator_add,
    logical.liftQubitOperator_add,
    logical.liftQubitOperator_smul, logical.liftQubitOperator_smul,
    logical.liftQubitOperator_smul, logical.liftQubitOperator_smul,
    logical.liftQubitOperator_one, logical.liftQubitOperator_pauliX,
    logical.liftQubitOperator_pauliZ, logical.liftQubitOperator_mul,
    logical.liftQubitOperator_pauliX, logical.liftQubitOperator_pauliZ]
private theorem commute_smul_right_operator
    (A B : Operator H) (h : Commute A B) (c : ℂ) :
    Commute A (c • B) := by
  rw [Commute]
  ext x
  simpa [Module.End.mul_apply] using
    congrArg (fun T : Operator H => c • T x) h.eq
private theorem commute_smul_left_operator
    (A B : Operator H) (h : Commute A B) (c : ℂ) :
    Commute (c • A) B :=
  (commute_smul_right_operator B A h.symm c).symm
private theorem commute_encodedObservable_projector
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (P : Operator K) (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (eta : DensityOperator Qubit.QubitSpace) :
    Commute (logical.encodedObservable eta) P := by
  rcases logical.liftQubitOperator_pauli_span ((2 : ℂ) • eta.toOperator) with
    ⟨cI, cZ, cX, cXZ, hspan⟩
  rw [← logical.liftQubitOperator_eq_encodedObservable eta, hspan]
  have hxP : Commute logical.x P := hPx.symm
  have hzP : Commute logical.z P := hPz.symm
  have hxzP : Commute (logical.x * logical.z) P := hxP.mul_left hzP
  have hIP : Commute (1 : Operator K) P := Commute.one_left P
  have hI := commute_smul_left_operator (1 : Operator K) P hIP cI
  have hZ := commute_smul_left_operator logical.z P hzP cZ
  have hX := commute_smul_left_operator logical.x P hxP cX
  have hXZ := commute_smul_left_operator (logical.x * logical.z) P hxzP cXZ
  exact ((hI.add_left hZ).add_left hX).add_left hXZ
private theorem jumpProtected_encodedObservable
    [Fintype ι]
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (J : ι → Operator K) (P : Operator K)
    (hPz : Commute P logical.z)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (eta : DensityOperator Qubit.QubitSpace) :
    JumpProtected J (logical.encodedObservable eta) P := by
  rcases logical.liftQubitOperator_pauli_span ((2 : ℂ) • eta.toOperator) with
    ⟨cI, cZ, cX, cXZ, hspan⟩
  rw [← logical.liftQubitOperator_eq_encodedObservable eta, hspan]
  have hXZ : JumpProtected J (logical.x * logical.z) P :=
    hprotectedX.mul_of_commute_projector hprotectedZ hPz.symm
  exact (((JumpProtected.one J P).smul cI).add (hprotectedZ.smul cZ))
    |>.add (hprotectedX.smul cX)
    |>.add (hXZ.smul cXZ)
private theorem encodedObservable_isSymmetric
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) :
    (logical.encodedObservable eta).IsSymmetric := by
  rw [← logical.liftQubitOperator_eq_encodedObservable eta]
  unfold ThermalEncoding.PauliLikePair.liftQubitOperator
  apply (logical.factorization.isPositive_conjOperator ?_).isSymmetric
  exact ThermalEncoding.tensorMap_positive ((2 : ℂ) • eta.toOperator)
    (1 : Operator logical.AuxiliarySpace)
    (eta.positive.smul_of_nonneg (by norm_num)) LinearMap.isPositive_one
end
end QEC.Semantics
end

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.clbtFiniteQuantumSystemComplete
namespace QEC.Semantics
theorem _root_.solution
    {K ι : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    [Nontrivial K] [Fintype ι]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : ι → Operator K) (P : Operator K)
    (hP : IsStarProjection P)
    (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (hHx : Commute hamiltonian logical.x)
    (hHz : Commute hamiltonian logical.z)
    (hPH : Commute P hamiltonian)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (hstationary : lindbladDissipator J
      (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta).toOperator = 0) :
    ∃ Enc : QuantumChannel Qubit.QubitSpace K,
      ∃ Dec : QuantumChannel K Qubit.QubitSpace,
        (∀ eta : DensityOperator Qubit.QubitSpace,
          Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
        ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤
            8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) := by
  let sigma := logical.auxiliaryGibbsState hamiltonian hHz hhamiltonian beta
  let rho := logical.physicalGibbsState hamiltonian hHz hhamiltonian beta
  let Enc := logical.thermalEncoding sigma
  let Dec := logical.thermalDecoding
  refine ⟨Enc, Dec, ?_, ?_⟩
  · intro eta
    exact logical.thermalDecoding_thermalEncoding_density sigma eta
  · intro eta t ht
    let O := logical.encodedObservable eta
    have hOrhoEq : Enc eta.toOperator = O * rho.toOperator := by
      rw [show rho = logical.thermalReferenceState sigma from
        logical.physicalGibbsState_eq_thermalReferenceState
          hamiltonian hHz hhamiltonian beta]
      exact logical.thermalEncoding_eq_encodedObservable_mul sigma eta
    have hprotectedO : JumpProtected J O P :=
      jumpProtected_encodedObservable logical J P hPz hprotectedX hprotectedZ eta
    have hOsym : O.IsSymmetric := encodedObservable_isSymmetric logical eta
    have hOP : Commute O P :=
      commute_encodedObservable_projector logical P hPx hPz eta
    have hOH : Commute O hamiltonian :=
      commute_encodedObservable_projector logical hamiltonian hHx hHz eta
    have hPrho : Commute P rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian P hHx hHz
        hhamiltonian hPH beta
    have hOrho : Commute O rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian O hHx hHz
        hhamiltonian hOH beta
    have hHrho : Commute hamiltonian rho.toOperator :=
      logical.commute_physicalGibbsState hamiltonian hamiltonian hHx hHz
        hhamiltonian (Commute.refl hamiltonian) beta
    have hHencoded : Commute hamiltonian (Enc eta.toOperator) := by
      rw [hOrhoEq]
      exact hOH.symm.mul_right hHrho
    have hencodedSym : (Enc eta.toOperator).IsSymmetric :=
      Enc.map_isSymmetric eta.positive.isSymmetric
    have htime := finiteLindbladEvolution_traceNorm_sub_le_time_mul
      hamiltonian J hhamiltonian (Enc eta.toOperator) hencodedSym hHencoded t ht
    have hlocal :
        traceNorm (lindbladDissipator J (Enc eta.toOperator)) ≤
          8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
      rw [hOrhoEq]
      exact clbtFourBlockGeneratorEstimate J O P rho hprotectedO hOsym hP hOP
        hOrho hPrho hstationary
        (logical.encodedObservable_operatorNorm_le_two eta)
    have hscaled := mul_le_mul_of_nonneg_left hlocal ht
    calc
      traceNorm
          (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
              |>.mapDensity (Enc.mapDensity eta)).toOperator -
            (Enc.mapDensity eta).toOperator) =
          traceNorm
            (finiteLindbladEvolutionLinearMap hamiltonian J t
              (Enc eta.toOperator) - Enc eta.toOperator) := rfl
      _ ≤ t * traceNorm (lindbladDissipator J (Enc eta.toOperator)) := htime
      _ ≤ t * (8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho) := hscaled
      _ = 8 * t * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring
end QEC.Semantics
