-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:10.797913+00:00
-- url     : https://prove2.me/submissions/53be05b0-fd73-4290-b991-362f45eebf17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_one_b05efafad2d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd

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
theorem _root_.solution {ι : Type*} (f : MvPolynomial ι L)
    (h : gaussNormOf (normAbv L) f ≤ 1) (n : ℕ) : gaussNormOf (normAbv L) (f ^ n) ≤ 1 := by
  induction n with
  | zero => rw [pow_zero]; exact gaussNorm_one.le
  | succ n ih => rw [pow_succ]; exact mul_le_one_of_gaussNorm ih h
end GroundTheory.Heights₂.Heights.GaussNormBasic
