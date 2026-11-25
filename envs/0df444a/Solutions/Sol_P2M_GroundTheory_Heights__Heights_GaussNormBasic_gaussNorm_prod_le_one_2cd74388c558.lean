-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:11.805594+00:00
-- url     : https://prove2.me/submissions/ee2f1646-0b11-4fb0-b1e2-cdef4133123f

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
theorem _root_.solution {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L)
    (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ 1) :
    gaussNormOf (normAbv L) (∏ b ∈ s, f b) ≤ 1 :=
  Finset.prod_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ 1)
    (fun _ _ ha hb ↦ mul_le_one_of_gaussNorm ha hb) gaussNorm_one.le h
end GroundTheory.Heights₂.Heights.GaussNormBasic
