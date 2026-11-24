-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_bdC_db7c19f2a798
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:11.356339+00:00
-- url     : https://prove2.me/submissions/311e1943-1429-4e09-a3a6-1e45213c921b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_d_99991395a567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_c_injective_5ccb4502175c
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
theorem _root_.solution (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by
  refine rel_succ.mpr ⟨X.c n y₀, (hX.c_d n y₀).symm, ?_⟩
  have hu : X.up n (X.c n y₀) = 0 := by
    apply hX.shift.c_injective n
    rw [map_zero]
    exact hX.vc0 n y₀
  rw [hu]
  exact Rel.zero n X.shift
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
