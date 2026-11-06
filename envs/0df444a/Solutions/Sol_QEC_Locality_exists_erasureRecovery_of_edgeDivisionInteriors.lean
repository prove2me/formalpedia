-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_edgeDivisionInteriors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:33.180413+00:00
-- url     : https://prove2.me/submissions/d24cad27-9f10-4f95-be2b-3d9a81d8ef04

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_edgeDivisionInteriors_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_bgklSmallBoundaryCorrectable
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled


set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (regions : m → Finset (ι × ι)) (active : Finset m)
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    (hSmall : ∀ i, i ∈ active →
      ((edgeDivisionInterior regions active i).card : ℝ) ≤
        Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : ∀ i, i ∈ active →
      4 * (fixedGeneratorOuterBoundaryFinset P
        (edgeDivisionInterior regions active i)).card ≤ d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro i hi
    exact bgklSmallBoundaryCorrectable P d hd hdn hDistance beta exponent
      hProfile hexponent (edgeDivisionInterior regions active i)
        (hSmall i hi) (hBoundary i hi)
  · intro i hi j hj hij
    exact edgeDivisionInteriors_fixedGeneratorDecoupled P hDivision hi hj hij
end QEC.Locality
