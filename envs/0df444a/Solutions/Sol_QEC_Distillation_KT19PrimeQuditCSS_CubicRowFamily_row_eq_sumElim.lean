-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.row_eq_sumElim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:23.00483+00:00
-- url     : https://prove2.me/submissions/222d4996-d1f4-48cc-a404-52f4eeb21736

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS

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
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_633
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_634
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_635
namespace QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
theorem _root_.solution (R : CubicRowFamily p Logical Stabilizer Site) :
    R.row = Sum.elim R.logicalRow R.stabilizerRow := by
  funext index
  cases index <;> rfl
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
