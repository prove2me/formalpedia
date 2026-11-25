-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:29:25.975813+00:00
-- url     : https://prove2.me/submissions/891b05ac-3541-40b3-88cf-d3ca47cb6c15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_closure_le_d777fdd60b50

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution {f : dualStdModelField K i} (hf : f ∈ Subfield.closure (Set.range (u K i))) :
    ∃ d ∈ (psiZ K i).range, d ≠ 0 ∧ d * f ∈ (psiZ K i).range := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hf
  by_cases h0 : z = 0
  · exact ⟨1, one_mem _, one_ne_zero, by simp [h0]⟩
  · refine ⟨z, closure_le hz, h0, ?_⟩
    rw [mul_div_cancel₀ y h0]
    exact closure_le hy
end GroundTheory.Heights₂.Heights.StandardModelDualRank
