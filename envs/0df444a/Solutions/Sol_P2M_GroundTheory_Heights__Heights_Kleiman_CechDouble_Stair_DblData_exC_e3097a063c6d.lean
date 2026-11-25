-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_exC_e3097a063c6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:29.453308+00:00
-- url     : https://prove2.me/submissions/fc23bfbc-7356-45d4-88c3-6de0784aee04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_injective_5ccb4502175c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_a_eacda9130b18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_h_aff36e0c4b5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_vc0_3c2fabe2c488

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
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, X.dC n y = 0 → ∃ x, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX y hy
    have hh0 : X.h 0 0 (X.c 0 y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨x, hx⟩ := hX.ex_a 0 hh0
    exact ⟨x, rel_zero.mpr hx⟩
  | succ n ih =>
    intro X hX y hy
    have hh0 : X.h 0 (n + 1) (X.c (n + 1) y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨z, hz⟩ := hX.ex_h 0 n hh0
    have hd : X.shift.dC n (X.up n z) = 0 := by
      apply hX.shift.c_injective (n + 1)
      rw [map_zero]
      show X.h 1 n (X.v 0 n z) = 0
      rw [← X.comm_apply, hz, hX.vc0]
    obtain ⟨x, hx⟩ := ih X.shift hX.shift (X.up n z) hd
    exact ⟨x, rel_succ.mpr ⟨z, hz, hx⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
