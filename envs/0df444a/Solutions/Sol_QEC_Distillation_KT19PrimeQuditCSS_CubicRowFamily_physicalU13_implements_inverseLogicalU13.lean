-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_implements_inverseLogicalU13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:52:48.739243+00:00
-- url     : https://prove2.me/submissions/aa0831d7-526c-45b8-9a20-4b64a434edde

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13_has_hierarchy
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_intertwines_encodingLinearMap

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
theorem _root_.solution (R : CubicRowFamily p Logical Stabilizer Site)
    (hp : PrimeAtLeastFive p) :
    R.encodedCode.ImplementsLogicalGate R.physicalU13 R.logicalInverseU13 := by
  cases u13_has_hierarchy p hp
  intro psi
  change _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p
      (R.encodingLinearMap psi) =
    R.encodingLinearMap (R.logicalInverseU13 psi)
  exact R.physicalU13_intertwines_encodingLinearMap psi
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
