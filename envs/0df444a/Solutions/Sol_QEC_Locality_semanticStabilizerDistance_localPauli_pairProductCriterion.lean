-- Prove2me | solution 1 for QEC.Locality.semanticStabilizerDistance_localPauli_pairProductCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:09:22.328877+00:00
-- url     : https://prove2.me/submissions/e785f827-bd2f-4bf0-86df-21c96268754b

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Theorems.Thm_QEC_Locality_weight_relative_embeddedLocalPauli_le_selected_card
import Theorems.Thm_QEC_Coding_StabilizerCode_semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (Q : StabilizerCode.SourceValidBinary ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q d)
    (S : FiniteSubsystem ι) (hSelected : S.selected.card < d) :
    ∀ p q : LocalPauliWordIndex S,
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) ∨
        ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (embeddedLocalPauli S p))
            (embeddedLocalPauli S q)) := by
  rcases
      (StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
        Q d).1 hDistance with
    ⟨_witness, _witnessNormalizer, _witnessOutside, _witnessWeight, hLeast⟩
  intro p q
  by_cases hGenerated : Q.1.InGeneratedGroupUpToSign
      (binaryMul (binaryDagger (embeddedLocalPauli S p))
        (embeddedLocalPauli S q))
  · exact Or.inl hGenerated
  · right
    intro hNormalizer
    have hDistanceLe := hLeast
      (binaryMul (binaryDagger (embeddedLocalPauli S p))
        (embeddedLocalPauli S q)) hNormalizer hGenerated
    have hWeightLe := weight_relative_embeddedLocalPauli_le_selected_card S p q
    exact (Nat.not_le_of_gt hSelected) (hDistanceLe.trans hWeightLe)
end QEC.Locality
