-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_not_relativeMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:25:24.321625+00:00
-- url     : https://prove2.me/submissions/165f0025-a70f-4458-b6f7-639ee7b0143e

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_zero_relativeSector_empty

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BH12EvenFamily
theorem _root_.solution (d : Nat) :
    ¬ RelativeMinimumDistance (family 0).evenCode.dual (family 0).rowCode.dual d := by
  rintro ⟨x, hxDual, hxRow, _⟩
  exact hxRow (zero_relativeSector_empty x |>.mp hxDual)
end QEC.Distillation.Triorthogonal.BH12EvenFamily
