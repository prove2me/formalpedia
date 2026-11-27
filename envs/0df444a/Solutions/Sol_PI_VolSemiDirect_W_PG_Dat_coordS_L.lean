-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.coordS_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:09.837442+00:00
-- url     : https://prove2.me/submissions/48c0d356-f1c1-4ff0-99a2-5eef65b0ccba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sum_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm


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
theorem _root_.solution (H : D.Hyp) {w : Fin r → n → A} (hw : ∀ a, IsW D (w a)) (s : Fin r → Fin r → A)
    (a b : Fin r) : D.h (D.f a) (D.L w s (D.f b)) = s a b := by
  have key : ∀ a', D.h (D.f a) (D.e a') = if a' = a then 1 else 0 := by
    intro a'
    rw [h_symm H, H.ef]
    split_ifs <;> simp
  have hwb : (∀ c, D.h (D.e c) (w b) = 0) ∧ (∀ c, D.h (D.f c) (w b) = 0) ∧ D.h D.z (w b) = 0 :=
    hw b
  rw [L_f H]
  simp [h_add_right, h_sum_right, h_smul_right, H.ff, hwb.2.1 a, key]
end PI.VolSemiDirect.W.PG.Dat
