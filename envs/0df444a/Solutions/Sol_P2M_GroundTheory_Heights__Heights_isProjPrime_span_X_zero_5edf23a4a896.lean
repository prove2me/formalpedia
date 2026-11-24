-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isProjPrime_span_X_zero_5edf23a4a896
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:35.718229+00:00
-- url     : https://prove2.me/submissions/fc5c15a1-823c-4031-8d98-9c150b265583

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (F : Type*) [Field F] :
    IsProjPrime (Ideal.span {(X 0 : MvPolynomial (Fin 2) F)}) where
  isPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  isHomog := by
    rw [isHomogIdeal_iff]
    refine Ideal.homogeneous_span _ _ fun x hx => ⟨1, ?_⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_homogeneousSubmodule]
    exact isHomogeneous_X _ _
  isRelevant := ⟨1, by
    rw [Ideal.mem_span_singleton]
    intro h
    have := (X_dvd_X (R := F)).mp h
    exact absurd this (by decide)⟩
end GroundTheory.Heights₂.Heights
