-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:07.576425+00:00
-- url     : https://prove2.me/submissions/0bad1a0c-7dcb-4ed0-9e60-c841190de63e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_add_le

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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - (if sg i then (absE β : ℝ) else 0)) (ddiv (onLetter i β) F) := by
  have h := (hV2 L sg r S).2.1 i β F
  have := vala_of_add_le _ h hF
  convert this using 1
  split_ifs <;> simp [sub_eq_add_neg]
end Formalism.MainNotions.PlaneGram
