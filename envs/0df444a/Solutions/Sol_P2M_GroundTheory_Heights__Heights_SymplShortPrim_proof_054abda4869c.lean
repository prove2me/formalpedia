-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplShortPrim_proof_054abda4869c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:40.3885+00:00
-- url     : https://prove2.me/submissions/89518493-29e9-44fc-945e-63f99a2a4c92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplShortPrim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplShortPrim_intVec_smul_63230d9938e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplShortPrim_qf_smul_5c62df27a8af

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open PSymplShortPrim
namespace GroundTheory.Heights₂.Heights
namespace SymplShortPrim
theorem _root_.solution : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega
end SymplShortPrim
end GroundTheory.Heights₂.Heights
