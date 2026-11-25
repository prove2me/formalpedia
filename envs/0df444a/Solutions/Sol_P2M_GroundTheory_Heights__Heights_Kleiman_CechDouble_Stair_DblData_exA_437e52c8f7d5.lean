-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exA_437e52c8f7d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:28.64813+00:00
-- url     : https://prove2.me/submissions/7b52537f-10ab-4dd5-b3ae-5528621c0bee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_up_surj_a97217a79961
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_d_fdddd4d4648e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_cocycle_ed5d92292b8a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX x hx
    have hv : X.v 0 0 (X.a 0 x) = 0 := by rw [← hX.a_d, hx, map_zero]
    obtain ⟨y, hy⟩ := hX.ex_c 0 hv
    exact ⟨y, rel_zero.mpr hy.symm⟩
  | succ n ih =>
    intro X hX x hx
    obtain ⟨w, hw⟩ := ih X.shift hX.shift x hx
    obtain ⟨z, rfl⟩ := X.up_surj n w
    have hc := (cocycle n X.shift hX.shift x (X.up n z) hw).2
    have h1 : X.h 1 n (X.v 0 n z) = 0 := by
      have := congrArg (X.shift.c (n + 1)) hc
      rw [map_zero] at this
      exact this
    have h2 : X.v 0 (n + 1) (X.h 0 n z) = 0 := by rw [X.comm_apply]; exact h1
    obtain ⟨y, hy⟩ := hX.ex_c (n + 1) h2
    exact ⟨y, rel_succ.mpr ⟨z, hy.symm, hw⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
