-- Prove2me | solution 1 for PI.LevelKSplit.W.Loc.dl_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:14:35.560917+00:00
-- url     : https://prove2.me/submissions/b5d7cd60-7be0-45bc-bd25-6708ee2fa510

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Theorems.Thm_PI_LevelKSplit_W_Loc_dl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
omit [CommRing O] [Algebra O B]
namespace PI.LevelKSplit.W.Loc
theorem _root_.solution (c : Fin n → B) (v : Fin r → Fin n → B) (d : Fin r → B) (b : Fin r)
    (h : ∀ a, c ⬝ᵥ v a = if a = b then 1 else 0) : dl c (∑ a, d a • v a) = d b := by
  simp [map_sum, dl_apply, dotProduct_smul, h]
end PI.LevelKSplit.W.Loc
