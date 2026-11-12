-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_relativeSector_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:40:50.904379+00:00
-- url     : https://prove2.me/submissions/3e3d9a3e-7020-4d04-9a2b-cd331fe8eae9

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_zero_evenCode_dual_eq_rowCode_dual

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (x : Word (ZMod 2) (Column 0)) :
    x ∈ (family 0).evenCode.dual.carrier ↔
      x ∈ (family 0).rowCode.dual.carrier := by
  rw [zero_evenCode_dual_eq_rowCode_dual]
end QEC.Distillation.Triorthogonal.BH12EvenFamily
