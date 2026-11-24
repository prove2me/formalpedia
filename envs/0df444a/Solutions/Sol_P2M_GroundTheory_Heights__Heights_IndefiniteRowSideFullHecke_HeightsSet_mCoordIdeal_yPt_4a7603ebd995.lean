-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_mCoordIdeal_yPt_4a7603ebd995
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:57.496715+00:00
-- url     : https://prove2.me/submissions/f7b857e7-f008-4881-930e-b055451cec89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_subsingleton_pt_2e0858fe9b58

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
theorem _root_.solution : mCoordIdeal (ι := PBlk 1) yPt = ⊥ := by
  have hf : ∀ f : MRing (PBlk 1), mConeMap yPt f =
      map (Int.castRingHom ℚ) (rename (fun p : Σ _ : Unit, PBlk 1 () ↦ p.1) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
    | mul_X p n hp => simp [mConeMap, yPt] at hp ⊢; rw [hp]
  have hinj : Function.Injective (mConeMap (ι := PBlk 1) yPt) := by
    intro f g hfg
    rw [hf, hf] at hfg
    have := subsingleton_pt
    exact rename_injective _ (fun a b _ ↦ Subsingleton.elim a b)
      (map_injective _ Int.cast_injective hfg)
  rw [mCoordIdeal]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
