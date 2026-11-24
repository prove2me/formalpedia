-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:56.713904+00:00
-- url     : https://prove2.me/submissions/3af11f56-141e-4773-bc85-81e17afc1409

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688


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
theorem _root_.solution {ι : Type*} {a b : MvPolynomial ι L}
    (ha : gaussNormOf (normAbv L) a ≤ 1) (hb : gaussNormOf (normAbv L) b ≤ 1) :
    gaussNormOf (normAbv L) (a * b) ≤ 1 :=
  (gaussNormOf_mul_le isNonarchimedean_normAbv a b).trans
    (mul_le_one₀ ha (gaussNormOf_nonneg _ b) hb)
end GroundTheory.Heights₂.Heights.GaussNormBasic
