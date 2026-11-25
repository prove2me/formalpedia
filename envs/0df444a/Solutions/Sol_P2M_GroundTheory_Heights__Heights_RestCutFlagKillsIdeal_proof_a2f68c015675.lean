-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutFlagKillsIdeal_proof_a2f68c015675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:07.059317+00:00
-- url     : https://prove2.me/submissions/caa84d66-df94-4ea6-b79f-d84fd8c9d249

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutFlagKillsIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_flagIntegral_sum_7c1da116bb5f

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights
namespace RestCutFlagKillsIdeal
theorem _root_.solution (h₁ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₂ : RestCutIdealSum.Statement) : RestCutFlagKillsIdeal.Statement := by
  intro f N A hA
  obtain ⟨G, rfl⟩ := h₂ f N A hA
  rw [flagIntegral_sum]
  refine Finset.sum_eq_zero fun i _ => h₁ f N ((i.1 : ℕ) + 1) i.2 (G i) (by omega) ?_
  have := i.1.isLt
  omega
end RestCutFlagKillsIdeal
end GroundTheory.Heights₂.Heights
