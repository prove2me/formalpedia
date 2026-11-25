-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:13.03416+00:00
-- url     : https://prove2.me/submissions/68360ea8-5b38-4360-8b68-638919608f29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula

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
theorem _root_.solution (f : ℕ) (τ : Fin f) (x : ℕ) :
    ∑ _σ ∈ Finset.univ.erase τ, x = (f - 1) * x := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Top
