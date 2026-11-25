-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:04.522007+00:00
-- url     : https://prove2.me/submissions/7c1c9a4b-4f39-4317-a09b-962ea89882c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)) = hsymm σ ℚ n := by
  rw [PowerSeries.coeff_prod, hsymm_eq_sum_finsuppAntidiag]
  simp [geomSeries, PowerSeries.coeff_mk]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
