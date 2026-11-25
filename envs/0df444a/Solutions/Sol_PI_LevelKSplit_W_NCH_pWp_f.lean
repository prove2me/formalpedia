-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.pWp_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:54.943745+00:00
-- url     : https://prove2.me/submissions/9f32564d-709b-4470-87ee-9b653bc58832

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_apply
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
private theorem hLap_lemma (D : Dat A n r) (x v : n → A) : D.hL x v = D.h x v := rfl
variable {D : Dat A n r}
private theorem pXap_lemma_10 (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]
private theorem pXvap_lemma_11 (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]
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
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (H : D.Hyp) (c : Fin r) : pWp D (D.f c) = 0 := by
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, H.ff, H.ef]
end PI.LevelKSplit.W.NCH
