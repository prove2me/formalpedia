-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exA_d751e04b00d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:44.23016+00:00
-- url     : https://prove2.me/submissions/fd0e5118-e0c9-4923-8996-bf9dc292e582

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_a_d_ca60db49e2cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_c_fba45879ce2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_cocycle_8537d20491da

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
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
