-- Prove2me | solution 1 for QEC.Semantics.tracePairing_spectralSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:40.584907+00:00
-- url     : https://prove2.me/submissions/785b92ad-9eb1-428f-9a7f-114baf7cd902

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_spectralSign_mul_of_isSymmetric
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



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
    tracePairing A (spectralSign A) =
      LinearMap.trace Complex H (positivePart A) +
        LinearMap.trace Complex H (negativePart A) := by
  change LinearMap.trace Complex H ((spectralSign A).toLinearMap * A) = _
  have hmul := congrArg ContinuousLinearMap.toLinearMap
    (spectralSign_mul_of_isSymmetric A hA)
  rw [show (spectralSign A).toLinearMap * A =
      ((LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻).toLinearMap by
    simpa using hmul]
  simp [positivePart, negativePart]
end QEC.Semantics
