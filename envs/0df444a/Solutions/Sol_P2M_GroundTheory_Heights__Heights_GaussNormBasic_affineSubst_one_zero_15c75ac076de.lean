-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:20.907788+00:00
-- url     : https://prove2.me/submissions/9fc1d665-2642-4bb6-90ef-19fa9bfdbed7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι L) :
    affineSubst (1 : Matrix ι ι L) 0 g = g := by
  unfold affineSubst
  have : (fun i ↦ ∑ j, C ((1 : Matrix ι ι L) i j) * X j + C ((0 : ι → L) i)) =
      (X : ι → MvPolynomial ι L) := by
    funext i
    simp [Matrix.one_apply]
  rw [this, bind₁_X_left]
  rfl
end GroundTheory.Heights₂.Heights.GaussNormBasic
