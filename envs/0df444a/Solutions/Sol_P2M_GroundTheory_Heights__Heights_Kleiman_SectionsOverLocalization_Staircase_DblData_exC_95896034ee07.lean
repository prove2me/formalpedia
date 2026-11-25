-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exC_95896034ee07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:45.585795+00:00
-- url     : https://prove2.me/submissions/0be169f5-3766-4543-9d66-af50701fff60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_d_ad3e77ed426f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_injective_3c88a6526558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_a_4dea343c93d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_vc0_4035bdd75d01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
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
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
