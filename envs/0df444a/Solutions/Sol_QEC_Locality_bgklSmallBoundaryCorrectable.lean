-- Prove2me | solution 1 for QEC.Locality.bgklSmallBoundaryCorrectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:35:26.987829+00:00
-- url     : https://prove2.me/submissions/c36ae6e5-076c-444c-befa-081c846230e2

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_BGKLSeparatorTree_node

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (W : Finset ι)
    (hSmall : (W.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P W).card ≤ d) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset W).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset W).complementSystem P.semanticCode
        (finiteSubsystemOfFinset W).erasureChannelFromRegister recovery := by
  let _ : 0 < Fintype.card ι := hd.trans_le hdn
  let _ : 0 < 1 - exponent := sub_pos.mpr hexponent
  let tree := buildBGKLSeparatorTree P d hd W
  exact exists_erasureRecovery_of_BGKLSeparatorTree_node
    P d hd hDistance hProfile tree hSmall hBoundary tree
      (BGKLSeparatorTree.IsNode.root tree)
end QEC.Locality
