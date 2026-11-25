-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_f_pX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:17.309546+00:00
-- url     : https://prove2.me/submissions/dede0ffa-d6e4-4d86-bb5b-82132404e043

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sum_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (a : Fin r) (u : n → A) : D.h (D.f a) (D.pX u) = D.h (D.f a) u := by
  have key : ∀ a', D.h (D.f a) (D.e a') = if a' = a then 1 else 0 := by
    intro a'
    rw [h_symm H, H.ef]
    split_ifs <;> simp
  rw [pX_apply, h_sum_right]
  simp [h_smul_right, key]
end PI.VolSemiDirect.W.PG.Dat
