-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_kerA_426174a2df2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:22.209549+00:00
-- url     : https://prove2.me/submissions/17058d80-ef81-4adb-be6f-f953899259c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_a_d_ca60db49e2cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_a_injective_c939b1bb02d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_injective_3c88a6526558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_a_4dea343c93d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac

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
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, Rel n X x 0 → x ∈ bdry X.dA n := by
  intro n
  induction n with
  | zero =>
    intro X hX x hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.a_injective 0 (by rw [hr', map_zero]))
  | succ n ih =>
    intro X hX x hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hz0 : X.h 0 n z = 0 := by rw [hz, map_zero]
    show x ∈ LinearMap.range (X.dA n)
    rcases n with _ | m
    · obtain ⟨x₀, hx₀⟩ := hX.ex_a 0 hz0
      have hr' := rel_zero.mp hr
      refine LinearMap.mem_range.mpr ⟨x₀, hX.a_injective 1 ?_⟩
      rw [hX.a_d, hx₀]
      exact hr'.symm
    · obtain ⟨z', hz'⟩ := hX.ex_h 0 m hz0
      have hu : X.up (m + 1) z = X.shift.dC m (X.up m z') := by
        apply hX.shift.c_injective (m + 1)
        show X.v 0 (m + 1) z = X.h 1 m (X.v 0 m z')
        rw [← hz', X.comm_apply]
      rw [hu] at hr
      have h0 := bdC m X.shift hX.shift (X.up m z')
      have hs : Rel (m + 1) X.shift x 0 := by
        have h1 : (x, X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := hr
        have h2 : ((0 : X.shift.A (m + 1)), X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := h0
        have h3 : Rel (m + 1) X.shift (x - (0 : X.A (m + 1 + 1))) (X.shift.dC m (X.up m z') - X.shift.dC m (X.up m z')) :=
          (relSub (m + 1) X.shift).sub_mem h1 h2
        rw [sub_zero, sub_self] at h3
        exact h3
      exact ih X.shift hX.shift x hs
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
