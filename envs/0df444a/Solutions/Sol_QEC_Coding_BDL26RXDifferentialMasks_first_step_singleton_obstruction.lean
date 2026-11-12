-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.first_step_singleton_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:48:40.814743+00:00
-- url     : https://prove2.me/submissions/e90ed7c5-4cc6-41be-afb3-34849fd35bfa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_shared_unselected_basis_obstruction

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    maskWord (nativeRegion S depth ⟨0,hd⟩ (by rfl) {(0 : BaseQubit)})
        (nativeDifferential S depth ⟨0,hd⟩ (canonicalBasisWord (4 : BaseQubit))) ≠
      nativeDifferential S depth ⟨0,hd⟩
        (maskWord {(0 : BaseQubit)} (canonicalBasisWord (4 : BaseQubit))) := by
  apply shared_unselected_basis_obstruction S depth ⟨0,hd⟩ (by rfl)
    {(0 : BaseQubit)} (0 : BaseQubit) (4 : BaseQubit) (0 : BaseZ)
  · exact Finset.mem_singleton_self (0 : BaseQubit)
  · change (4 : BaseQubit) ∉ ({(0 : BaseQubit)} : Finset BaseQubit)
    decide
  · change baseTannerSquarePresentation.qz (0 : BaseQubit) (0 : BaseZ) = true
    decide
  · change baseTannerSquarePresentation.qz (4 : BaseQubit) (0 : BaseZ) = true
    decide
end QEC.Coding.BDL26RXDifferentialMasks
