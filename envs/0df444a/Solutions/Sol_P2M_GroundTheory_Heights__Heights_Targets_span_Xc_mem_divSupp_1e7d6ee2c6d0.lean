-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_span_Xc_mem_divSupp_1e7d6ee2c6d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:04.439437+00:00
-- url     : https://prove2.me/submissions/b478a664-9da4-46ce-8987-f9961cd86aa8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength

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
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) := by
  refine ⟨?_, fun k => ⟨1, ?_⟩⟩
  · rw [bot_sup_eq]
    have : (Ideal.span {(Xc 2 0 : MRing (PBlk 2))}).IsPrime :=
      (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · obtain ⟨⟩ := k
    intro h
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp h
    have := congrArg (MvPolynomial.eval (fun q : Σ k : Unit, PBlk 2 k => if q.2 = 0 then (0 : ℤ) else 1)) hg
    simp [Xc] at this
end GroundTheory.Heights₂.Heights.Targets
