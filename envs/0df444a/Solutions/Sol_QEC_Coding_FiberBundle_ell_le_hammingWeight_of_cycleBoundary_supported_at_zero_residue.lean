-- Prove2me | solution 1 for QEC.Coding.FiberBundle.ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:07:07.294693+00:00
-- url     : https://prove2.me/submissions/6588f8ed-7764-4a1b-90ec-6aa9f770d6a2

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_apply
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
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
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0)
    (hBoundaryNonzero :
      cycleFiberChainBoundary (ell * ell) v ≠ 0) :
    ell ≤ HammingWeight v := by
  classical
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hSquare : ell ≤ ell * ell := by nlinarith
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hBoundaryNonzero
  change cycleFiberChainBoundary (ell * ell) v j ≠ 0 at hj
  have hjResidue : fiberResidue ell j = 0 :=
    hBoundarySupport j hj
  have hBlockBound
      (start : ZMod (ell * ell))
      (hStartResidue : fiberResidue ell start = 0)
      (hSome :
        ∃ k : Fin ell,
          v (start + (k.val : ZMod (ell * ell))) ≠ 0) :
      ell ≤ HammingWeight v := by
    have hRun :
        ∀ k : Nat, k < ell →
          v (start + (k : ZMod (ell * ell))) = v start := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
          have hkPrev : k < ell := by omega
          have hResidueNe :
              fiberResidue ell
                (start + ((k + 1 : Nat) : ZMod (ell * ell))) ≠ 0 := by
            rw [map_add, hStartResidue, zero_add]
            change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
              (((k + 1 : Nat) : ZMod (ell * ell))) ≠ 0
            rw [ZMod.castHom_apply,
              ZMod.cast_natCast (R := ZMod ell)
                (dvd_mul_right ell ell)]
            intro hzero
            have hval := congrArg ZMod.val hzero
            rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
            omega
          have hBoundaryZero :
              cycleFiberChainBoundary (ell * ell) v
                (start + ((k + 1 : Nat) : ZMod (ell * ell))) = 0 := by
            by_contra hne
            exact hResidueNe (hBoundarySupport _ hne)
          rw [cycleFiberChainBoundary_apply
            (ell * ell) (by nlinarith)] at hBoundaryZero
          have hStep :
              v (start + ((k + 1 : Nat) : ZMod (ell * ell))) =
                v ((start + ((k + 1 : Nat) :
                  ZMod (ell * ell))) - 1) := by
            have hneg := eq_neg_of_add_eq_zero_left hBoundaryZero
            simpa [ZMod.neg_eq_self_mod_two] using hneg
          calc
            v (start + ((k + 1 : Nat) : ZMod (ell * ell))) =
                v ((start + ((k + 1 : Nat) :
                  ZMod (ell * ell))) - 1) := hStep
            _ = v (start + (k : ZMod (ell * ell))) := by
              congr 2
              push_cast
              abel
            _ = v start := ih hkPrev
    rcases hSome with ⟨k₀, hk₀⟩
    have hStartNonzero : v start ≠ 0 := by
      rw [hRun k₀.val k₀.isLt] at hk₀
      exact hk₀
    let supportEmbedding :
        Fin ell → ↥(hammingSupport v) :=
      fun k => ⟨start + (k.val : ZMod (ell * ell)), by
        simp only [hammingSupport, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [hRun k.val k.isLt]
        exact hStartNonzero⟩
    have hInjective : Function.Injective supportEmbedding := by
      intro k l hkl
      apply Fin.ext
      have hCoord :
          start + (k.val : ZMod (ell * ell)) =
            start + (l.val : ZMod (ell * ell)) :=
        congrArg Subtype.val hkl
      have hCast :
          (k.val : ZMod (ell * ell)) =
            (l.val : ZMod (ell * ell)) :=
        add_left_cancel hCoord
      have hVal := congrArg ZMod.val hCast
      rw [ZMod.val_natCast_of_lt
          (lt_of_lt_of_le k.isLt hSquare),
        ZMod.val_natCast_of_lt
          (lt_of_lt_of_le l.isLt hSquare)] at hVal
      exact hVal
    have hCard :
        Fintype.card (Fin ell) ≤
          Fintype.card ↥(hammingSupport v) :=
      Fintype.card_le_of_injective supportEmbedding hInjective
    rw [Fintype.card_fin, Fintype.card_coe] at hCard
    simpa [HammingWeight] using hCard
  rw [cycleFiberChainBoundary_apply
    (ell * ell) (by nlinarith)] at hj
  by_cases hvj : v j = 0
  · have hvPrev : v (j - 1) ≠ 0 := by
      intro hzero
      apply hj
      rw [hvj, hzero, zero_add]
    let start : ZMod (ell * ell) := j - (ell : Nat)
    have hStartResidue : fiberResidue ell start = 0 := by
      change fiberResidue ell (j - (ell : Nat)) = 0
      rw [map_sub, hjResidue]
      have hEllResidue :
          fiberResidue ell
            ((ell : Nat) : ZMod (ell * ell)) = 0 := by
        simp [fiberResidue]
      rw [hEllResidue, sub_zero]
    apply hBlockBound start hStartResidue
    let k : Fin ell := ⟨ell - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hCoord :
        start + (k.val : ZMod (ell * ell)) = j - 1 := by
      dsimp [start, k]
      have hEllCast :
          ((ell : Nat) : ZMod (ell * ell)) =
            ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
        calc
          ((ell : Nat) : ZMod (ell * ell)) =
              (((ell - 1) + 1 : Nat) : ZMod (ell * ell)) := by
                congr 1
                omega
          _ = ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
                rw [Nat.cast_add, Nat.cast_one]
      rw [hEllCast]
      abel
    rw [hCoord]
    exact hvPrev
  · apply hBlockBound j hjResidue
    exact ⟨0, by simpa using hvj⟩
end QEC.Coding.FiberBundle
