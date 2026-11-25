-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.mapW_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:08.842331+00:00
-- url     : https://prove2.me/submissions/18d3ae72-80f9-4340-aa17-bb8025be332d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_span_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left


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
theorem _root_.solution {S Si : (n → A) →ₗ[A] (n → A)} (hSSi : ∀ v, S (Si v) = v) (hU : D.Uni S)
    (hXi : D.MapX Si) (hZi : Si D.z - D.z ∈ Submodule.span A (Set.range D.e)) : D.MapW S := by
  intro w hw
  refine ⟨fun b => ?_, ?_⟩
  · rw [← hSSi (D.e b), hU]
    exact h_span_left (hXi b) hw.1
  · rw [← hSSi D.z, hU]
    have hz : Si D.z = D.z + (Si D.z - D.z) := by abel
    rw [hz, h_add_left, hw.2.2, h_span_left hZi hw.1, add_zero]
end PI.LevelKSplit.W.SemiG.Dat
