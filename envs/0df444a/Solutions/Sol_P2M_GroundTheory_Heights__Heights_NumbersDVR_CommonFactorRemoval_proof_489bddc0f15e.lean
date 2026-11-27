-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CommonFactorRemoval_proof_489bddc0f15e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:36.386333+00:00
-- url     : https://prove2.me/submissions/d8255dd2-98a9-4104-bc9d-225512c8eb14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RatDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace CommonFactorRemoval
theorem _root_.solution (hmul : DivCycleMul.Statement.{u}) : CommonFactorRemoval.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g q s hf hg hq _ hH c L

  have hrat : ∀ W : Ideal (MRing ι O), W.IsPrime → f ∉ W → g ∉ W → q ∉ W →
      ratDiv W (f * q) (g * q) = ratDiv W f g := by
    intro W hW hfW hgW hqW
    funext G
    simp only [ratDiv, hmul O K ι W f q hW hfW hqW, hmul O K ι W g q hW hgW hqW, Pi.add_apply]
    ring
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [hrat P hP.multiProj.isPrime hf hg hq]
  · unfold cutIdentityRightSide cycEval
    congr 1
    funext W
    by_cases hW : divCycle P s W = 0
    · simp [hW]
    · dsimp only
      split_ifs with hϖ
      · rfl
      · obtain ⟨h1, h2, h3⟩ := hH W hW hϖ
        rw [hrat W (isPrime_of_divCycle_ne_zero hW) h1 h2 h3]
end CommonFactorRemoval
end GroundTheory.Heights₂.Heights.NumbersDVR
