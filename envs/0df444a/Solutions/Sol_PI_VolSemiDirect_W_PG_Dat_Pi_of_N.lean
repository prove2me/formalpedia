-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_of_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:00.503614+00:00
-- url     : https://prove2.me/submissions/c1f4fb55-510a-4052-b1ed-da96a04226ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pW


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
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)}
    (hN : ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e))
    (v : n → A) : D.Pi S v = v := by
  have hw := isW_pW H v
  have h1 : D.pW (S (D.pW v)) = D.pW v := by
    have e1 : S (D.pW v) = D.pW v + (S (D.pW v) - D.pW v) := by abel
    rw [e1, map_add, pW_pW H, pW_span H (hN _ hw.1), add_zero]
  rw [Pi_apply, h1, pW_apply]
  abel
end PI.VolSemiDirect.W.PG.Dat
