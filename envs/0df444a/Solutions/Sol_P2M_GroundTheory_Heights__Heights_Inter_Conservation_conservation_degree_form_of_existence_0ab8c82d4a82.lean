-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_conservation_degree_form_of_existence_0ab8c82d4a82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:11.877131+00:00
-- url     : https://prove2.me/submissions/27245498-6e50-4b0c-8f16-14e28d8e9ccc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_vertR_C_prime_81226bff0cf2

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
namespace GroundTheory.Heights₂.Heights.Inter
namespace Conservation
theorem _root_.solution (hE : ThmIExists.Statement) (hC : Conservation.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement := by
  intro K _ ι _ P n L p hP hL hp
  obtain ⟨I, hI⟩ := hE
  obtain ⟨h1, h2⟩ := hC K ι (I K ι) (hI K ι) P n L p hP hL hp
  have h := h1.symm.trans h2
  rw [Conservation.vertR_C_prime P L hp] at h
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' h
end Conservation
end GroundTheory.Heights₂.Heights.Inter
