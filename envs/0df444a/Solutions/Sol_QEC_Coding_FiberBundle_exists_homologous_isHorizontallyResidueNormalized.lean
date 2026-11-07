-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:33:47.552009+00:00
-- url     : https://prove2.me/submissions/9fe893e2-f8bd-4620-91d8-9039389ea54d

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalResiduePotential_oneStepSlideCluster_lt
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_add_boundary2_mem_middleCycleCode
import Theorems.Thm_QEC_Coding_FiberBundle_IsHomologyClassWeightMinimal_add_boundary2
import Theorems.Thm_QEC_Coding_FiberBundle_exists_homologyClassWeightMinimal
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
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
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
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


attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rcases exists_homologyClassWeightMinimal
      baseSample twistSample z hz with
    ⟨zMin, hzMin, hMinWeight, hMinHomologous, hMinClass⟩
  let candidates : Finset
      (Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) :=
    Finset.univ.filter (fun c =>
      HammingWeight (zMin + boundary2 D c) = HammingWeight zMin)
  have hZeroCandidate : (0 : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [map_zero, add_zero]⟩
  obtain ⟨c, hcCandidate, hleast⟩ :=
    Finset.exists_min_image candidates
      (fun d => horizontalResiduePotential
        (zMin + boundary2 D d))
      ⟨0, hZeroCandidate⟩
  let z' := zMin + boundary2 D c
  have hcWeight :
      HammingWeight z' = HammingWeight zMin := by
    exact (Finset.mem_filter.mp hcCandidate).2
  have hz' : z' ∈ (chainComplex D).middleCycleCode.carrier := by
    exact add_boundary2_mem_middleCycleCode
      baseSample twistSample zMin c hzMin
  have hClass' :
      IsHomologyClassWeightMinimal baseSample twistSample z' := by
    exact hMinClass.add_boundary2
      baseSample twistSample zMin c hcWeight
  have hPrimeMinHomologous :
      z' + zMin ∈ (chainComplex D).middleBoundaryCode.carrier := by
    apply ((chainComplex D).mem_middleBoundaryCode_iff
      (z' + zMin)).2
    refine ⟨c, ?_⟩
    funext q
    change boundary2 D c q =
      (zMin q + boundary2 D c q) + zMin q
    have hmm : zMin q + zMin q = 0 := by
      calc
        zMin q + zMin q = zMin q + (-zMin q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    calc
      boundary2 D c q =
          (zMin q + zMin q) + boundary2 D c q := by
            rw [hmm, zero_add]
      _ = (zMin q + boundary2 D c q) + zMin q := by abel
  have hPrimeHomologous :
      z' + z ∈ (chainComplex D).middleBoundaryCode.carrier := by
    have hsum := Submodule.add_mem _
      hPrimeMinHomologous hMinHomologous
    have heq :
        (z' + zMin) + (zMin + z) = z' + z := by
      funext q
      change (z' q + zMin q) + (zMin q + z q) = z' q + z q
      have hmm : zMin q + zMin q = 0 := by
        calc
          zMin q + zMin q = zMin q + (-zMin q) := by
            rw [ZMod.neg_eq_self_mod_two]
          _ = 0 := add_neg_cancel _
      calc
        (z' q + zMin q) + (zMin q + z q) =
            z' q + (zMin q + zMin q) + z q := by abel
        _ = z' q + z q := by rw [hmm, add_zero]
    rw [heq] at hsum
    exact hsum
  have hNormalized : IsHorizontallyResidueNormalized z' := by
    by_contra hNotNormalized
    have hBad :
        ∃ b : Fin (4 * r), ∃ i : ZMod (ell * ell),
          z' (Sum.inl (b, i)) ≠ 0 ∧ fiberResidue ell i ≠ 0 := by
      unfold IsHorizontallyResidueNormalized at hNotNormalized
      push Not at hNotNormalized
      exact hNotNormalized
    rcases hBad with ⟨b, i, hSupport, hResidue⟩
    let root : Fin (4 * r) × ZMod (ell * ell) := (b, i)
    let h := horizontalClusterSubchain
      baseSample twistSample z' root
    let e : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) :=
      c + oneStepSlideTwoChain h
    have hSlideWeight :
        HammingWeight
            (oneStepSlide baseSample twistSample z' h) =
          HammingWeight z' := by
      exact
        (hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
          baseSample twistSample z' hz' hClass' root).1
    have hWordEq :
        zMin + boundary2 D e =
          oneStepSlide baseSample twistSample z' h := by
      funext q
      change zMin q +
          boundary2 D (c + oneStepSlideTwoChain h) q =
        (zMin q + boundary2 D c q) +
          boundary2 D (oneStepSlideTwoChain h) q
      rw [map_add]
      change zMin q +
          (boundary2 D c q +
            boundary2 D (oneStepSlideTwoChain h) q) =
        (zMin q + boundary2 D c q) +
          boundary2 D (oneStepSlideTwoChain h) q
      abel
    have heCandidate : e ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ e, ?_⟩
      rw [hWordEq, hSlideWeight, hcWeight]
    have hLeastPotential := hleast e heCandidate
    have hPotentialStrict :
        horizontalResiduePotential
            (oneStepSlide baseSample twistSample z' h) <
          horizontalResiduePotential z' := by
      exact horizontalResiduePotential_oneStepSlideCluster_lt
        baseSample twistSample z' root hSupport hResidue
    change horizontalResiduePotential z' ≤
      horizontalResiduePotential (zMin + boundary2 D e) at hLeastPotential
    rw [hWordEq] at hLeastPotential
    exact (not_lt_of_ge hLeastPotential) hPotentialStrict
  refine ⟨z', ?_, ?_, ?_, hNormalized⟩
  · simpa [D] using hz'
  · rw [hcWeight]
    exact hMinWeight
  · simpa [D] using hPrimeHomologous
end QEC.Coding.FiberBundle
