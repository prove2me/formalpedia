-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_e_pX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:28.450791+00:00
-- url     : https://prove2.me/submissions/ca5e9ecd-de25-4b3e-a401-41e6e584675f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable {D : Dat A n r}
private theorem hL_apply_lemma (x y : n → A) : D.hL x y = D.h x y := rfl
end Dat
end PI.LevelKSplit.W.SemiG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) (b : Fin r) (u : n → A) : D.h (D.e b) (D.pX u) = 0 := by
  rw [← hL_apply_lemma]
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
  simp only [hL_apply_lemma, H.ee, smul_zero, Finset.sum_const_zero]
end PI.LevelKSplit.W.SemiG.Dat
