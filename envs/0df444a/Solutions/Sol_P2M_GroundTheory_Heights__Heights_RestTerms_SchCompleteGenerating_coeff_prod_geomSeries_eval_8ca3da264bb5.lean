-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coeff_prod_geomSeries_eval_8ca3da264bb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:50.740285+00:00
-- url     : https://prove2.me/submissions/815dfbdb-bc2b-4591-8e32-8e8b8f54479e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchCompleteGenerating
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291


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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.SchCompleteGenerating
namespace GroundTheory.Heights₂.Heights.RestTerms.SchCompleteGenerating
theorem _root_.solution {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by
  rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]
end GroundTheory.Heights₂.Heights.RestTerms.SchCompleteGenerating
