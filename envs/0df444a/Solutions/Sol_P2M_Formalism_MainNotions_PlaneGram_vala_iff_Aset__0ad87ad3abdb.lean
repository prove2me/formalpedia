-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vala_iff_Aset__0ad87ad3abdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:46.66445+00:00
-- url     : https://prove2.me/submissions/06f5f408-fdc9-4bd5-820c-61ef610ec3d7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff_Aset


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
theorem _root_.solution {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (θ : ℝ)
    (F : MvPolynomial (L × Fin r) K) : vala sg S θ F ↔ F ∈ Aset sg S ⌈θ⌉ := by
  exact vala_iff_Aset sg S θ F
end Formalism.MainNotions.PlaneGram
