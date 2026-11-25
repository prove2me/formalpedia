-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:16.29421+00:00
-- url     : https://prove2.me/submissions/d674a456-f77f-48d9-ad85-91cc4f9d22c8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) (a : ℕ) : 0 ≤ lg p r a := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ (a : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  linarith [Real.logb_nonneg hp1 h1]
end Formalism.MainNotions.PlaneGram
