-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isArithVar_pointZ_46bf9e092250
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.535914+00:00
-- url     : https://prove2.me/submissions/cf8d0b28-7582-4a9b-89f0-1493e7813cf2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution : IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf ↦ absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ ↦ ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 1 ()) = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
