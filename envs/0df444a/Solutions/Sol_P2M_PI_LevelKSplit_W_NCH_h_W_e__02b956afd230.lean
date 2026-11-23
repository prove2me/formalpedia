-- Prove2me | solution 1 for P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:32.432739+00:00
-- url     : https://prove2.me/submissions/6cb1587a-91d7-4b34-b6f6-e7b9591e9f41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
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
private theorem hswap_lemma_6 (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [Dat.h, Formalism.UG.hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
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
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.e b) = 0 := by
  unfold IsWp at hw
  rw [hswap_lemma_6 H, hw.1 b, map_zero]
end PI.LevelKSplit.W.NCH
