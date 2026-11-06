-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_caseDGeK_badQubits_edgeStrips
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:19:45.465689+00:00
-- url     : https://prove2.me/submissions/5db77834-e571-4ec7-82ab-378a5159ded7

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι)
    (s : Finset α)
    (hCard : ∀ a, a ∈ caseDGeKPieceIndices s →
      (caseDGeKPieceFamily badQubits edgeStrips a).selected.card < d)
    (hDecoupled : ∀ a, a ∈ caseDGeKPieceIndices s →
      ∀ b, b ∈ caseDGeKPieceIndices s → a ≠ b →
        P.fixedGeneratorDecoupled
          ((caseDGeKPieceFamily badQubits edgeStrips a).selected : Set ι)
          ((caseDGeKPieceFamily badQubits edgeStrips b).selected : Set ι)) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        P.semanticCode
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro a ha
    exact semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance (caseDGeKPieceFamily badQubits edgeStrips a) (hCard a ha)
  · exact hDecoupled
end QEC.Locality
