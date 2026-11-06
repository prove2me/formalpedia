-- Prove2me | solution 1 for QEC.Semantics.projectedTail_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:11:19.382752+00:00
-- url     : https://prove2.me/submissions/9b7897a4-8caa-43a2-b684-69ae6783aa99

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
theorem _root_.solution (P A : Operator H) (hP : IsStarProjection P)
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (projectedTail P A) := by
  have hQ : IsStarProjection (1 - P) := hP.one_sub
  have h := hA.conj_adjoint (1 - P)
  have hQsym : (1 - P).IsSymmetricProjection :=
    LinearMap.isStarProjection_iff_isSymmetricProjection.mp hQ
  rw [hQsym.2.adjoint_eq] at h
  change LinearMap.IsPositive ((1 - P).comp (A.comp (1 - P)))
  exact h
end QEC.Semantics
