-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:24.684697+00:00
-- url     : https://prove2.me/submissions/8bbfeec7-46f5-4366-ad19-42af4deb6916

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_bind__le_378a88d78935
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305

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
theorem _root_.solution {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g :=
  gaussNorm_bind₁_le _ (fun i ↦ gaussNorm_linearForm_le _ _ (hB i) (ha i)) g
end GroundTheory.Heights₂.Heights.GaussNormBasic
