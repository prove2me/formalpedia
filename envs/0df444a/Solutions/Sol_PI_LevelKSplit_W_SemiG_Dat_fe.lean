-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:19.239733+00:00
-- url     : https://prove2.me/submissions/40238010-7b78-4891-8608-50a6eae9aa4f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
variable {D}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) (a b : Fin r) : D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [h_symm H, H.ef b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]
end PI.LevelKSplit.W.SemiG.Dat
