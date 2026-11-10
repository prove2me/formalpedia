-- Prove2me | solution 1 for QEC.Distillation.KT19Protocol.KT19DistillationFamily.dualWordCarrier_eq_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:33:04.692338+00:00
-- url     : https://prove2.me/submissions/ff345114-54c1-4df7-ab94-15022b850ef5

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
import Theorems.Thm_QEC_Distillation_KT19Protocol_KT19DistillationFamily_kt19Routing_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dual
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
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
private theorem wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
    (left right : Word (ZMod p) (ZMod p))
    (hselected : restrictSelected p k left = 0) :
    wordPairing (restrictKept p k left) (restrictKept p k right) =
      wordPairing left right := by
  classical
  letI selectedPunctureSubtypeFintype :
      Fintype {point : ZMod p // point ∈ selectedPunctureLocations p k} :=
    Subtype.fintype _
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : ZMod p => point ∈ selectedPunctureLocations p k)
      (fun point => left point * right point)
  let complementKept :
      {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k} ≃
        KeptPunctureLocation p k :=
    { toFun := fun point => ⟨point.1,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation p k, left point.1 * right point.1) =
    ∑ point : ZMod p, left point * right point
  have hselectedSum :
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    have hpoint : left point.1 = 0 := by
      simpa using congrFun hselected
        (⟨point.1, point.2⟩ : SelectedPunctureLocation p k)
    rw [hpoint]
    simp
  have hcomplement :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : ZMod p, left point * right point := by
    rw [hselectedSum, zero_add] at hsplit
    exact hsplit
  have hequiv :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : KeptPunctureLocation p k, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement
private theorem puncturedComplementary_le_shortenedDual
    (family : KT19DistillationFamily p l k) :
    (puncturedReedSolomonCode p (p - l) k).carrier ≤
      (shortenedReedSolomonCode p l k).dual.carrier := by
  rcases family.admissible with ⟨_, _, _, hlp, _⟩
  intro word hword
  refine ((shortenedReedSolomonCode p l k).mem_dual word).2 ?_
  intro shortened hshortened
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨fullWord, hfullWord, hrestrictWord⟩
  rcases (mem_shortenedReedSolomonCode shortened).1 hshortened with
    ⟨fullShortened, hfullShortened, hselected, hrestrictShortened⟩
  have hfullWordDual : fullWord ∈ (reedSolomonCode p l).dual.carrier := by
    rw [reedSolomonCode_dual p l hlp]
    simpa using hfullWord
  have horthogonal := (reedSolomonCode p l).orthogonal_of_mem_dual
    hfullWordDual hfullShortened
  rw [← hrestrictWord, ← hrestrictShortened]
  calc
    wordPairing (restrictKept p k fullWord)
        (restrictKept p k fullShortened) =
        wordPairing (restrictKept p k fullShortened)
          (restrictKept p k fullWord) := by
      simp only [wordPairing_apply, dotProduct_comm]
    _ = wordPairing fullShortened fullWord :=
      wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
        fullShortened fullWord hselected
    _ = 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using horthogonal
private theorem shortenedDual_eq_complementaryPunctured
    (family : KT19DistillationFamily p l k) :
    (shortenedReedSolomonCode p l k).dual.carrier =
      (puncturedReedSolomonCode p (p - l) k).carrier := by
  rcases family.admissible with ⟨_, _, hkl, hlp, _⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hcomplementLength : p - l ≤ p - k := by omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact puncturedComplementary_le_shortenedDual family
  · change Dimension (puncturedReedSolomonCode p (p - l) k) =
      Dimension (shortenedReedSolomonCode p l k).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      puncturedReedSolomonCode_dimension p (p - l) k hkp hcomplementLength,
      shortenedReedSolomonCode_dimension p l k hkp hkl hlp]
    have hcard : Fintype.card (KeptPunctureLocation p k) = p - k := by
      simpa using keptPunctureLocations_card p k hkp
    simp only [Length, hcard]
    omega
end KT19DistillationFamily
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
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
open QEC.Distillation.KT19Protocol.KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
namespace QEC.Distillation.KT19Protocol.KT19DistillationFamily
theorem _root_.solution
    (family : KT19DistillationFamily p l k) :
    (kt19StabilizerCode family.rowFamily).dual.carrier =
      (puncturedReedSolomonCode p (p - l) k).carrier := by
  have hcarrier :
      (kt19StabilizerCode family.rowFamily).carrier =
        (shortenedReedSolomonCode p l k).carrier := by
    simpa [kt19StabilizerCode] using family.stabilizerCarrier_eq_shortened
  rw [LinearCode.dual_carrier, hcarrier]
  simpa only [LinearCode.dual_carrier] using
    shortenedDual_eq_complementaryPunctured family
end QEC.Distillation.KT19Protocol.KT19DistillationFamily
