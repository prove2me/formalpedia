-- Prove2me | solution 1 for QEC.Coding.hammingSupport_add_subset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:13:38.366522+00:00
-- url     : https://prove2.me/submissions/4274a5a7-8f15-40ee-8d9e-44af3a9a5164

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [DecidableEq ι] [Fintype ι] (x y : Word F ι) :
    hammingSupport (x + y) ⊆ hammingSupport x ∪ hammingSupport y := by
  intro i hi
  simp [hammingSupport] at hi ⊢
  by_cases hx0 : x i = 0
  · right
    intro hy0
    exact hi (by simp [hx0, hy0])
  · left
    exact hx0
end QEC.Coding
