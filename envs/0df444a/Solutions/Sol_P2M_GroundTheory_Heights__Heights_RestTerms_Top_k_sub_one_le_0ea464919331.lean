-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:47.208495+00:00
-- url     : https://prove2.me/submissions/632cef1b-c31e-4994-91f8-0c271b9bd350

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorFormula

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
theorem _root_.solution (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by
  have : r + a ≤ r * a + 1 := by nlinarith
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
