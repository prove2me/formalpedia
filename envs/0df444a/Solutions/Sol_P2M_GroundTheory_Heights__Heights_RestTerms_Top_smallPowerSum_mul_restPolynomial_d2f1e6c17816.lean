-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:44.843315+00:00
-- url     : https://prove2.me/submissions/d67fd2ba-91f5-488b-85ae-6a25f2880b5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_zero_56f893cffc92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec


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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (k : ℕ) (hk : 2 ≤ k)
    (τ : Fin f) :
    smallPowerSum f r a c (k - 1) τ * restPolynomial f r a c =
      gmf f r a c (fun σ => if σ = τ then k - 1 else 0) (f * (r * a) + 1) := by
  rw [gmf, restPolynomial]
  have : ∏ σ, blockEmb f (r + a) σ
      (yEval r a c (extraFactor r (if σ = τ then k - 1 else 0))) =
      smallPowerSum f r a c (k - 1) τ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [Finset.prod_eq_one (fun σ hσ => by
      rw [if_neg (Finset.ne_of_mem_erase hσ), extraFactor_zero, map_one, map_one])]
    rw [if_pos rfl, extraFactor, if_neg (by omega), blockEmb_yEval_psum, mul_one]
  rw [this]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Top
