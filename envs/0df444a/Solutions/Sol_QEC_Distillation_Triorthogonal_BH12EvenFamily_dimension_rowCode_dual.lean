-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_rowCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:25:14.350333+00:00
-- url     : https://prove2.me/submissions/76e08c35-8997-444b-8db7-686982b5728d

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_rowCode
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (q : Nat) :
    Dimension (family q).rowCode.dual = 2 * logicalCount q + 5 := by
  rw [(family q).rowCode.dual_dimension_eq_length_sub_dimension,
    dimension_rowCode]
  change Fintype.card (Column q) - (logicalCount q + 3) = _
  rw [card_column]
  omega
end QEC.Distillation.Triorthogonal.BH12EvenFamily
