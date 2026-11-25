-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.pWp_sL_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:47.60275+00:00
-- url     : https://prove2.me/submissions/282db63e-9873-4520-a2f4-b7f6286262d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_of_isWp
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_e
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_f
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (c : Fin r) : pWp D (sL D half y (D.f c)) = y c := by
  rw [sL_f H hy, map_add, pWp_f H, zero_add, uv, map_add, pWp_of_isWp (hy c), map_sum]
  simp [pWp_e H]
end PI.LevelKSplit.W.NCH
