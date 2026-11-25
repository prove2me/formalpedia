-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_kerC_79b4646adddb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:31.093581+00:00
-- url     : https://prove2.me/submissions/4582d8ec-0281-4162-84ee-90008f392c8f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_up_surj_a97217a79961
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_injective_5ccb4502175c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_hh_18a00f98fcef

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
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
