-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isArithVar_projLine_149b03129df9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:48.566343+00:00
-- url     : https://prove2.me/submissions/d86698d4-5b94-4482-a2cd-c84897e44978

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 2 ()) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl
end GroundTheory.Heights₂.Heights.Inter
