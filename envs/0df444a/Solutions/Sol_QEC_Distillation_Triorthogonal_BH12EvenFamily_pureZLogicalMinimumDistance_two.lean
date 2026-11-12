-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.pureZLogicalMinimumDistance_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:44:49.593411+00:00
-- url     : https://prove2.me/submissions/335cb734-03cd-4942-97e7-76b1ba784bc3

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_relativeMinimumDistance_two

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution {q : Nat} (hq : 0 < q) :
    PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 :=
  relativeMinimumDistance_two hq
end QEC.Distillation.Triorthogonal.BH12EvenFamily
