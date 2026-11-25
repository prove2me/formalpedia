-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_coordIdeal_alt_e00026a6d73f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:54.768927+00:00
-- url     : https://prove2.me/submissions/472befb6-782c-4ca2-a89a-66de887bfcd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_aeval_alt_44907c1184c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_zero_fd50f88d740d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_homog_dehom_1e6d54fd090f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coeff_coneMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
theorem _root_.solution : coordIdeal ℤ x = ⊥ := by
  ext f
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hcomp : ∀ d, homogeneousComponent d f = 0 := fun d ↦ by
      have h1 : aeval x (homogeneousComponent d f) = 0 := by
        rw [← coeff_coneMap ℤ x f d]
        rw [coordIdeal, RingHom.mem_ker] at hf
        rw [hf, Polynomial.coeff_zero]
      rw [aeval_alt] at h1
      have h2 : dehom (homogeneousComponent d f) = 0 :=
        IsFractionRing.injective (Polynomial ℤ) Fld (by rw [h1, map_zero])
      rw [← homog_dehom (homogeneousComponent_isHomogeneous d f), h2, homog_zero]
    rw [Submodule.mem_bot, ← sum_homogeneousComponent f]
    simp [hcomp]
  · rw [Submodule.mem_bot] at hf
    rw [hf]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
