-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_kerC_72334999a815
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:24.859546+00:00
-- url     : https://prove2.me/submissions/df05636d-7712-4a0d-9f51-adf2b7ada7bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_d_ad3e77ed426f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_injective_3c88a6526558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_c_fba45879ce2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_hh_f82467743477

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
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, Rel n X 0 y → y ∈ bdry X.dC n := by
  intro n
  induction n with
  | zero =>
    intro X hX y hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.c_injective 0 (by rw [← hr', map_zero]))
  | succ n ih =>
    intro X hX y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hb := ih X.shift hX.shift (X.up n z) hr
    show y ∈ LinearMap.range (X.dC n)
    rcases n with _ | m
    · have hb0 : X.up 0 z = 0 := (Submodule.mem_bot R).mp hb
      have hv : X.v 0 0 z = 0 := by
        have := congrArg (X.shift.c 0) hb0
        rw [map_zero] at this
        exact this
      obtain ⟨y₀, hy₀⟩ := hX.ex_c 0 hv
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective 1 ?_⟩
      rw [hX.c_d, hy₀, hz]
    · have hb' : X.up (m + 1) z ∈ LinearMap.range (X.shift.dC m) := hb
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hb'
      obtain ⟨z', rfl⟩ := X.up_surj m w
      have e : X.v 0 (m + 1) (X.h 0 m z') = X.v 0 (m + 1) z := by
        rw [X.comm_apply]
        exact congrArg (X.shift.c (m + 1)) hw
      obtain ⟨y₀, hy₀⟩ := hX.ex_c (m + 1) (show X.v 0 (m + 1) (z - X.h 0 m z') = 0 by rw [map_sub, e, sub_self])
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective (m + 2) ?_⟩
      rw [hX.c_d, hy₀, map_sub, hX.hh, sub_zero, hz]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
