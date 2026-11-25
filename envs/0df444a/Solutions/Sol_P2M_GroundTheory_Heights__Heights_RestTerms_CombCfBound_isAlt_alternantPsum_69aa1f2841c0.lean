-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_isAlt_alternantPsum_69aa1f2841c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:50.836686+00:00
-- url     : https://prove2.me/submissions/d9c9bef3-c001-4464-8c2e-b96d106ad26e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
theorem _root_.solution (m : ℕ) (ρ : List ℕ) : IsAlt (alternantPsum m ρ) :=
  isAlt_vandermonde_mul_prod ρ
end GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
