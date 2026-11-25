-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:58.199828+00:00
-- url     : https://prove2.me/submissions/332c3442-ea89-4d72-97e3-1d5839bd5042

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_apply
import Theorems.Thm_P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
private theorem hy2_lemma_13 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.e b) = 0 :=
  h_W_e' H (hy a) b
section Sec
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
end Sec
end PI.LevelKSplit.W.NCH
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (c : Fin r) : sL D half y (D.e c) = D.e c := by
  simp [sL_apply, H.ee, hy2_lemma_13 H hy]
end PI.LevelKSplit.W.NCH
