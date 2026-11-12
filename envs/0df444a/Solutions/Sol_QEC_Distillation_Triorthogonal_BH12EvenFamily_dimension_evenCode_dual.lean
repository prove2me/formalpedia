-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_evenCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:25:21.102202+00:00
-- url     : https://prove2.me/submissions/accd7db8-d662-44a7-86c9-46eda5c6061f

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_evenCode
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (q : Nat) :
    Dimension (family q).evenCode.dual = 3 * logicalCount q + 5 := by
  rw [(family q).evenCode.dual_dimension_eq_length_sub_dimension,
    dimension_evenCode]
  change Fintype.card (Column q) - 3 = _
  rw [card_column]
  omega
end QEC.Distillation.Triorthogonal.BH12EvenFamily
