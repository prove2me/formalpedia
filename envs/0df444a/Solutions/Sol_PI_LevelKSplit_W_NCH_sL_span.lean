-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:04.366786+00:00
-- url     : https://prove2.me/submissions/591933df-7644-4733-bd13-9ed800cb5045

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_xp_of_span
import Theorems.Thm_P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_Xp

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
theorem _root_.solution {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) : sL D half y x = x := by
  rw [sL_Xp H hy (xp_of_span H hx)]
  have hz : ∀ b, D.h (y b) x = 0 := fun b => h_W_span' H (hy b) hx
  simp [hz]
end PI.LevelKSplit.W.NCH
