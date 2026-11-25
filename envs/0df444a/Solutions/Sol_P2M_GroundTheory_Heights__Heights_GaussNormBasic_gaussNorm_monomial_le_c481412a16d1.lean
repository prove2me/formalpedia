-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:00.616529+00:00
-- url     : https://prove2.me/submissions/6a43a8f6-5565-4497-a2d5-6cd4df9594a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813


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
omit [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution {ι : Type*} (d : ι →₀ ℕ) (b : L) :
    gaussNormOf (normAbv L) (monomial d b) ≤ ‖b‖ := by
  classical
  refine gaussNormOf_le _ (norm_nonneg b) fun m ↦ ?_
  rw [coeff_monomial, normAbv_apply]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.GaussNormBasic
