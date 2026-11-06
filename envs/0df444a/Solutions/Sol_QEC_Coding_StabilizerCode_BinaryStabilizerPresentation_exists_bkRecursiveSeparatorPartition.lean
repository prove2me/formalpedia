-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.exists_bkRecursiveSeparatorPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:17.141749+00:00
-- url     : https://prove2.me/submissions/9b4b55da-30b7-46dc-90a1-6fa1e470d794

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_exists_bkRecursivePartition
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_bkRecursivePartition_erasureRecoverable

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : SemanticStabilizerDistance P.code d)
    (hd : 0 < d) (vertices : Finset ι) :
    ∃ partition : BKRecursivePartition P.fixedGeneratorInteractionGraph d vertices,
      ∃ recovery : QuantumChannel
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).complementSystem
          P.semanticCode
          (familyUnionSubsystem (fun region : Finset ι => (⟨region⟩ : FiniteSubsystem ι))
            partition.pieces).erasureChannelFromRegister recovery := by
  rcases exists_bkRecursivePartition P.fixedGeneratorInteractionGraph d hd vertices with
    ⟨partition⟩
  exact ⟨partition, P.bkRecursivePartition_erasureRecoverable d hDistance vertices partition⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
