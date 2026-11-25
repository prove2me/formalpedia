-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_R1_equiv_smooth_0fb3f1843f02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:17.197179+00:00
-- url     : https://prove2.me/submissions/709134e5-ac63-416b-a9a0-e2108558457f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_isSectionOn_5e773a81802a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_vecEmpty_eq_elim0_909cf59b659a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace R1
theorem _root_.solution :
    (IndependenceOfSmoothMetric.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) ↔ R1.Statement := by
  constructor
  · rintro ⟨hind, hadd⟩ K _ ι _ P hP
    refine ⟨fun I J A s s' hA hs hs' => ?_, fun I A B s t hA hB hs ht => ?_⟩
    · rw [isSec_iff_isSectionOn] at hs hs'
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      rw [recR_family_eq hs (fun F t ht => hind K ι F P A s t hP hA hs ht) I J]
      exact hind K ι J P A s s' hP hA hs hs'
    · rw [isSec_iff_isSectionOn] at hs ht
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      exact hadd K ι I P A B s t hP hA hB hs ht
  · intro h
    refine ⟨fun K _ ι _ I P A s t hP hA hs ht => ?_, fun K _ ι _ I P A B s t hP hA hB hs ht => ?_⟩
    · have := (h K ι P hP).1 I I A s t hA ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this
    · have := (h K ι P hP).2 I A B s t hA hB ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this
end R1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
