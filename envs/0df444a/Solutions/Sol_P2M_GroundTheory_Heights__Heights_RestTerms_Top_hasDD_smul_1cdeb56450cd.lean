-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:48.679222+00:00
-- url     : https://prove2.me/submissions/1adea6cf-ba22-47ae-b950-eb5164c15bf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc

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
theorem _root_.solution {f N : ℕ} {H P : RootRing f N} (b : ℚ) (h : HasDD f N H P) :
    HasDD f N (b • H) (b • P) := by
  rw [HasDD, antisymmetrize_smul, h, mul_smul_comm]
end GroundTheory.Heights₂.Heights.RestTerms.Top
