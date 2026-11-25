-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coe_prod_one_sub_46d3c6e30d7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:39.091633+00:00
-- url     : https://prove2.me/submissions/1358b6a9-1943-4622-85e1-061aff779f28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchCompleteGenerating

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
theorem _root_.solution {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp
end GroundTheory.Heights₂.Heights.RestTerms.SchCompleteGenerating
