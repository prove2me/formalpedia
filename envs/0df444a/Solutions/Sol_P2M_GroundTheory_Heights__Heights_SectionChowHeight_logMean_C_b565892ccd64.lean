-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:42.272917+00:00
-- url     : https://prove2.me/submissions/4cf355a2-0c2e-4723-88a1-6537a47cfe2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionChowHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)
open GroundTheory.Heights₂.Heights.SectionChowHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SectionChowHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (k : ℕ) (z : ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (k + 1))
      (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ) = Real.log ‖z‖ := by
  have h := ObjectsHeight.mahler_eq_chowMean S hS (ObjectsHeight.ofPointMatrix S hS)
    (ObjectsHeight.ofPointMatrix_norm S hS) (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
  rw [mahler_C] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.SectionChowHeight
