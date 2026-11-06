-- Prove2me | solution 1 for QEC.Semantics.positivePart_sub_negativePart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:11:19.960822+00:00
-- url     : https://prove2.me/submissions/7b6aac25-5516-4064-81f0-c293beb661a8

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) (hA : A.IsSymmetric) :
    positivePart A - negativePart A = A := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsSymmetric := hA
  apply LinearMap.toContinuousLinearMap.injective
  change (LinearMap.toContinuousLinearMap A)⁺ -
      (LinearMap.toContinuousLinearMap A)⁻ = LinearMap.toContinuousLinearMap A
  exact CFC.posPart_sub_negPart _ hAclm.isSelfAdjoint
end QEC.Semantics
