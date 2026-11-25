-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_detForm_c907a9fb9d04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:33.202673+00:00
-- url     : https://prove2.me/submissions/d383e2b5-68c8-434c-aabe-34260aaf052b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_finIdeal_bot_609cd897da2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isMultihomog_detForm_ae74412cb508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_squarefree_detForm_5f14a536d456

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
theorem _root_.solution :
    IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1 (detForm ℂ) := by
  refine ⟨isMultihomog_detForm ℂ, squarefree_detForm, fun u => ?_⟩
  rw [finIdeal_bot]
  have key := Matrix.exists_mulVec_eq_zero_iff (M := (Matrix.of u : Matrix (Fin 2) (Fin 2) ℂ))
  rw [Matrix.det_fin_two] at key
  simp only [detForm, map_sub, map_mul, eval_X]
  constructor
  · intro h
    obtain ⟨z, hz, hz0⟩ := key.mpr (by simpa using h)
    exact ⟨z, (mem_conePts_bot z).mpr hz, fun j => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hz0 j⟩
  · rintro ⟨z, hz, hj⟩
    have h := key.mp ⟨z, (mem_conePts_bot z).mp hz, funext fun j => by
      simpa [Matrix.mulVec, dotProduct] using hj j⟩
    simpa using h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
