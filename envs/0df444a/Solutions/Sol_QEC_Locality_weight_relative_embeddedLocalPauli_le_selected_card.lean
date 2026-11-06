-- Prove2me | solution 1 for QEC.Locality.weight_relative_embeddedLocalPauli_le_selected_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:07:07.989467+00:00
-- url     : https://prove2.me/submissions/3b5c4031-aada-4d6a-baa6-65b40eefe306

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Theorems.Thm_QEC_Locality_support_relative_embeddedLocalPauli_subset

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
theorem _root_.solution (S : FiniteSubsystem ι)
    (p q : LocalPauliWordIndex S) :
    weight (binaryMul (binaryDagger (embeddedLocalPauli S p))
      (embeddedLocalPauli S q)) ≤ S.selected.card := by
  exact Finset.card_le_card (support_relative_embeddedLocalPauli_subset S p q)
end QEC.Locality
