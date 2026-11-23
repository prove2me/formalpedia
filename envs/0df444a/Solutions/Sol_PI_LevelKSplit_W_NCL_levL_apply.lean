-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:10.750687+00:00
-- url     : https://prove2.me/submissions/1efc5825-bc2a-43e3-9c04-f7ea478e6397

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
private theorem hL_apply_lemma (D : Dat A n r) (x y : n → A) : D.hL x y = D.h x y := rfl
variable {D : Dat A n r}
section Hyp
variable (H : D.Hyp)
include H
end Hyp
end PI.LevelKSplit.W.NCL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W x = pV D x + ∑ a, (∑ b, U a b * D.h (D.f b) x) • D.e a +
      ∑ d, (∑ b, W d b * D.h (D.e b) x) • D.f d := by
  simp only [levL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, hL_apply_lemma, Finset.sum_smul, smul_smul]
end PI.LevelKSplit.W.NCL
