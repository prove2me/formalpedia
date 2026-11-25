-- Prove2me | solution 1 for P2M_PI_LevelKSplit_W_NCH_h_W_span__a0509f779950
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:42.789857+00:00
-- url     : https://prove2.me/submissions/a80ba7e4-c7f3-454a-b78d-e147f2ecfe38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
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
private theorem hRsmul_lemma_4 (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  show (D.hL x) (c • y) = c * (D.hL x) y
  rw [map_smul, smul_eq_mul]
private theorem hRsum_lemma_5 (x : n → A) (g : Fin r → n → A) :
    D.h x (∑ i, g i) = ∑ i, D.h x (g i) := by
  show (D.hL x) (∑ i, g i) = ∑ i, (D.hL x) (g i)
  exact map_sum _ _ _
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
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsWp D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [hRsum_lemma_5, hRsmul_lemma_4, h_W_e' H hw]
end PI.LevelKSplit.W.NCH
