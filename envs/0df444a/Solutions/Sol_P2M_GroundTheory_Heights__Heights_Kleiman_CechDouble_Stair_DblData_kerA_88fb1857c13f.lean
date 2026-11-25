-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerA_88fb1857c13f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:30.431961+00:00
-- url     : https://prove2.me/submissions/afdd2db9-65b6-4556-ab40-d43d0acb4cf1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_d_fdddd4d4648e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_a_injective_237f2d3278a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_injective_5ccb4502175c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_a_eacda9130b18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_h_aff36e0c4b5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdC_db7c19f2a798

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
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
