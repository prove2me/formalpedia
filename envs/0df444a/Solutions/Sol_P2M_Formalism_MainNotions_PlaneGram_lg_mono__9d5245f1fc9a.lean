-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:14.983253+00:00
-- url     : https://prove2.me/submissions/4cb42379-058e-4a8b-9494-20358444ab1c

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {a b : ℕ} (hab : a ≤ b) :
    lg p r a ≤ lg p r b := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (a : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    positivity
  have hle : (a : ℝ) + r ≤ (b : ℝ) + r := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  linarith [Real.logb_le_logb_of_le hp1 hpos hle]
end Formalism.MainNotions.PlaneGram
