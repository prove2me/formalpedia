-- Prove2me | solution 1 for QEC.Coding.FiberBundle.weight_bound_for_all_corrections_of_nontrivial_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:30.070518+00:00
-- url     : https://prove2.me/submissions/5d3761cd-d882-490b-975a-92cfdaaefa75

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_IsNontrivialBaseCohomology_add_baseCoboundary_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_c0FibersNormalized_normalizeC0Fibers
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_exists_isWeightMinimal
import Theorems.Thm_QEC_Coding_FiberBundle_IsHorizontalWeightMinimal_normalized
import Theorems.Thm_QEC_Coding_FiberBundle_IsWeightMinimal_normalized
import Theorems.Thm_QEC_Coding_FiberBundle_horizontal_or_vertical_weight_of_normalized_weight_minimal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) v) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) v) := by
  rcases exists_isWeightMinimal baseSample twistSample x with
    ⟨u, hMinimal⟩
  let shiftedX := x + normalizationBaseShift baseSample u
  let normalizedU := normalizeC0Fibers u
  let normalizedRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) shiftedX +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) normalizedU
  let arbitraryRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) v
  have hShiftedNonzero : shiftedX ≠ 0 := by
    simpa [shiftedX, normalizationBaseShift] using
      (IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
        baseSample x hx (normalizationToggle u))
  have hNormalized : C0FibersNormalized normalizedU := by
    exact c0FibersNormalized_normalizeC0Fibers u
  have hNormalizedMinimal :
      IsWeightMinimal baseSample twistSample shiftedX normalizedU := by
    exact hMinimal.normalized baseSample twistSample x u
  have hRepresentativeEq :
      normalizedRepresentative =
        horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u := by
    exact horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
      baseSample twistSample x u
  have hWeightLe :
      HammingWeight normalizedRepresentative ≤
        HammingWeight arbitraryRepresentative := by
    rw [hRepresentativeEq]
    exact hMinimal v
  rcases
      horizontal_or_vertical_weight_of_normalized_weight_minimal
        baseSample twistSample shiftedX normalizedU hShiftedNonzero
        hNormalized hNormalizedMinimal hDelta hDegree hExpansion with
    hHorizontal | hVertical
  · left
    have hSector :
        HammingWeight (horizontalComponent normalizedRepresentative) ≤
          HammingWeight normalizedRepresentative := by
      rw [hammingWeight_eq_horizontal_add_vertical]
      omega
    exact hHorizontal.trans
      ((Nat.mul_le_mul_left 2 hSector).trans
        (Nat.mul_le_mul_left 2 hWeightLe))
  · right
    have hSector :
        HammingWeight (verticalComponent normalizedRepresentative) ≤
          HammingWeight normalizedRepresentative := by
      rw [hammingWeight_eq_horizontal_add_vertical]
      omega
    exact hVertical.trans_le
      ((Nat.mul_le_mul_left (100000 * Delta) hSector).trans
        (Nat.mul_le_mul_left (100000 * Delta) hWeightLe))
end QEC.Coding.FiberBundle
