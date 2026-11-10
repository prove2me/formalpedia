-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.p11AcceptedWord_hammingWeight_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:33:09.760325+00:00
-- url     : https://prove2.me/submissions/498af26d-447b-485d-989e-d90b0abd36d8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Theorems.Thm_QEC_Distillation_KT19Protocol_kt19AcceptedWord_iff_mem_stabilizerCode_dual
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedComplementaryReedSolomon_minimumDistance
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dual
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_stabilizerCarrier_eq_shortenedReedSolomon
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


attribute [local simp] QEC.Distillation.KT19Protocol.KT19DistillationFamily.kt19Routing_apply
section
noncomputable section
namespace QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
section Syndromes
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
private theorem p11_wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
    (left right : Word (ZMod 11) (ZMod 11))
    (hselected : restrictSelected 11 2 left = 0) :
    wordPairing (restrictKept 11 2 left) (restrictKept 11 2 right) =
      wordPairing left right := by
  classical
  letI selectedPunctureSubtypeFintype :
      Fintype {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2} :=
    Subtype.fintype _
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : ZMod 11 => point ∈ selectedPunctureLocations 11 2)
      (fun point => left point * right point)
  let complementKept :
      {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2} ≃
        KeptPunctureLocation 11 2 :=
    { toFun := fun point => ⟨point.1,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation 11 2, left point.1 * right point.1) =
    ∑ point : ZMod 11, left point * right point
  have hselectedSum :
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    have hpoint : left point.1 = 0 := by
      simpa using congrFun hselected
        (⟨point.1, point.2⟩ : SelectedPunctureLocation 11 2)
    rw [hpoint]
    simp
  have hcomplement :
      (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
        left point.1 * right point.1) =
        ∑ point : ZMod 11, left point * right point := by
    rw [hselectedSum, zero_add] at hsplit
    exact hsplit
  have hequiv :
      (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
        left point.1 * right point.1) =
        ∑ point : KeptPunctureLocation 11 2, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement
private theorem p11_puncturedSeven_le_shortenedFour_dual :
    (puncturedReedSolomonCode 11 7 2).carrier ≤
      (shortenedReedSolomonCode 11 4 2).dual.carrier := by
  intro word hword
  refine ((shortenedReedSolomonCode 11 4 2).mem_dual word).2 ?_
  intro shortened hshortened
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨fullWord, hfullWord, hrestrictWord⟩
  rcases (mem_shortenedReedSolomonCode shortened).1 hshortened with
    ⟨fullShortened, hfullShortened, hselected, hrestrictShortened⟩
  have hfullWordDual : fullWord ∈ (reedSolomonCode 11 4).dual.carrier := by
    rw [reedSolomonCode_dual 11 4 (by norm_num)]
    simpa using hfullWord
  have horthogonal := (reedSolomonCode 11 4).orthogonal_of_mem_dual
    hfullWordDual hfullShortened
  rw [← hrestrictWord, ← hrestrictShortened]
  calc
    wordPairing (restrictKept 11 2 fullWord)
        (restrictKept 11 2 fullShortened) =
        wordPairing (restrictKept 11 2 fullShortened)
          (restrictKept 11 2 fullWord) := by
      simp only [wordPairing_apply, dotProduct_comm]
    _ = wordPairing fullShortened fullWord :=
      p11_wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
        fullShortened fullWord hselected
    _ = 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using horthogonal
private theorem p11_shortenedFour_dual_eq_puncturedSeven :
    (shortenedReedSolomonCode 11 4 2).dual.carrier =
      (puncturedReedSolomonCode 11 7 2).carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact p11_puncturedSeven_le_shortenedFour_dual
  · change Dimension (puncturedReedSolomonCode 11 7 2) =
      Dimension (shortenedReedSolomonCode 11 4 2).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      puncturedReedSolomonCode_dimension 11 7 2 (by norm_num) (by norm_num),
      shortenedReedSolomonCode_dimension 11 4 2 (by norm_num) (by norm_num) (by norm_num)]
    have hcard : Fintype.card (KeptPunctureLocation 11 2) = 9 := by
      simpa using keptPunctureLocations_card 11 2 (by norm_num : 2 ≤ 11)
    simp [Length, hcard]
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
end KT19DistillationFamily
end Syndromes
end QEC.Distillation.KT19Protocol
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime
attribute [local instance] QEC.Distillation.KT19Protocol.p11NeZero
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
namespace QEC.Distillation.KT19Protocol
theorem _root_.solution
    (error : Word (ZMod 11) (KeptPunctureLocation 11 2))
    (haccepted : kt19AcceptedWord p11CubicRowFamily error) (herror : error ≠ 0) :
    3 ≤ HammingWeight error := by
  have hacceptedDual :
      error ∈ (kt19StabilizerCode p11CubicRowFamily).dual.carrier :=
    (kt19AcceptedWord_iff_mem_stabilizerCode_dual p11CubicRowFamily error).mp haccepted
  rw [LinearCode.mem_dual] at hacceptedDual
  have hshortenedDual :
      error ∈ (shortenedReedSolomonCode 11 4 2).dual.carrier := by
    rw [LinearCode.mem_dual]
    intro carrier hcarrier
    apply hacceptedDual carrier
    change carrier ∈ p11StabilizerCarrier
    rw [p11_stabilizerCarrier_eq_shortenedReedSolomon]
    exact hcarrier
  have hpunctured : error ∈ (puncturedReedSolomonCode 11 7 2).carrier := by
    rw [← p11_shortenedFour_dual_eq_puncturedSeven]
    exact hshortenedDual
  have hminimum : MinimumDistance (puncturedReedSolomonCode 11 7 2) 3 := by
    exact puncturedComplementaryReedSolomon_minimumDistance
      (p := 11) (l := 4) (k := 2) (by norm_num [Admissible])
  rcases hminimum with ⟨_, _, _, _, hleast⟩
  exact hleast error hpunctured herror
end QEC.Distillation.KT19Protocol
