-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.453988+00:00
-- url     : https://prove2.me/submissions/55e471d4-2291-4e74-afe0-d4e82bae5d86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution {ι : Type*} (g g' : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (g + g') ≤
      max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') := by
  refine gaussNormOf_le _ ((gaussNormOf_nonneg _ g).trans (le_max_left _ _)) fun m ↦ ?_
  rw [coeff_add]
  exact (isNonarchimedean_normAbv _ _).trans
    (max_le_max (le_gaussNormOf _ g m) (le_gaussNormOf _ g' m))
end GroundTheory.Heights₂.Heights.GaussNormBasic
