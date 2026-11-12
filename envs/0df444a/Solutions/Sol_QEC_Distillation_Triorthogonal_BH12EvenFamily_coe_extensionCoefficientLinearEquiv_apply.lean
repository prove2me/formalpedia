-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:28:05.560207+00:00
-- url     : https://prove2.me/submissions/26f58c84-0d05-46a9-ac63-83890f2f599a

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution {q : Nat}
    (a : OddRow q) (c : Sum Unit EvenRow → ZMod 2) :
    ((extensionCoefficientLinearEquiv a c : (singleOddExtensionCode a).carrier) :
      Word (ZMod 2) (Column q)) = extensionCombination a c :=
  rfl
end QEC.Distillation.Triorthogonal.BH12EvenFamily
