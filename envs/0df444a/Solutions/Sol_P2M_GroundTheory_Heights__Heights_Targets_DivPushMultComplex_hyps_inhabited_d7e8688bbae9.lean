-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_DivPushMultComplex_hyps_inhabited_d7e8688bbae9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:46.837124+00:00
-- url     : https://prove2.me/submissions/2fc24fd3-9949-42f6-9463-af1f3f3b3653

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Targets
namespace DivPushMultComplex
theorem _root_.solution :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).minimalPrimes ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes := by
  have hprime : (Ideal.span {(Xc 2 0 : MRing (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hprimeC : (Ideal.span {(X ⟨(), 0⟩ : MRingOver ℂ (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  refine ⟨?_, ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · rw [IsHorizontal, eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hc
    obtain ⟨q, hq⟩ := hc
    have h := congrArg constantCoeff hq
    simpa using h
  · rw [Ideal.map_span, Set.image_singleton, Xc, map_X, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
end DivPushMultComplex
end GroundTheory.Heights₂.Heights.Targets
