-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_Xp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:35.4858+00:00
-- url     : https://prove2.me/submissions/a4d3c1b8-f026-4e88-8f4d-0b43c0369d9a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_apply

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
theorem _root_.solution {v : n → A} (hv : Xp D v) : sL D half y v = v - ∑ b, D.h (y b) v • D.e b := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  simp [sL_apply, hv']
end PI.LevelKSplit.W.NCH
