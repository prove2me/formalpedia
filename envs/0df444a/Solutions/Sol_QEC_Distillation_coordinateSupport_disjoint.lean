-- Prove2me | solution 1 for QEC.Distillation.coordinateSupport_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:08.388964+00:00
-- url     : https://prove2.me/submissions/430faf7d-783c-44ac-b026-bf312e97acd4

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.mem_coordinateSupport

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]
namespace QEC.Distillation
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    {first second : ι} (hne : first ≠ second) :
    Disjoint (coordinateSupport first) (coordinateSupport second) := by
  apply Finset.disjoint_left.mpr
  intro coordinate hfirst hsecond
  have hfirst' : coordinate.2 = first := mem_coordinateSupport.mp hfirst
  have hsecond' : coordinate.2 = second := mem_coordinateSupport.mp hsecond
  exact hne (hfirst'.symm.trans hsecond')
end QEC.Distillation
