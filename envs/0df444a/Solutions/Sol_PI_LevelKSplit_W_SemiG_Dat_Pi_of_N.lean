-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_of_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:00.798048+00:00
-- url     : https://prove2.me/submissions/9780730b-1fc8-4332-bd3f-f9b7283d270a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_span
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isW_pW
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_pW


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
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)}
    (hN : ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e))
    (v : n → A) : D.Pi S v = v := by
  have hw := isW_pW H v
  have h1 := pW_span H (hN _ hw.1)
  rw [map_sub, pW_pW H, sub_eq_zero] at h1
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, h1]
  simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]
  abel
end PI.LevelKSplit.W.SemiG.Dat
