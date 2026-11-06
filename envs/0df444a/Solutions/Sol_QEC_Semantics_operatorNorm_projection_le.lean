-- Prove2me | solution 1 for QEC.Semantics.operatorNorm_projection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:13.053332+00:00
-- url     : https://prove2.me/submissions/fef4221b-c7d0-4177-97e7-54ab8f90412d

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
theorem _root_.solution (P : Operator H) (hP : IsStarProjection P) :
    operatorNorm P ≤ 1 := by
  have hPc : IsStarProjection (LinearMap.toContinuousLinearMap P) :=
    LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr hP
  obtain ⟨U, _hUProjection, hU⟩ :=
    isStarProjection_iff_eq_starProjection.mp hPc
  rw [operatorNorm, hU]
  exact U.starProjection_norm_le
end QEC.Semantics
