-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:48.783705+00:00
-- url     : https://prove2.me/submissions/e3e1bc36-7985-4eab-b90f-bd7dc5059ab7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_d9b41f76efc3

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
theorem _root_.solution {n : ℕ} (f : Fin n → dualStdModelField K i)
    (hf : ∀ k, f k ∈ Subfield.closure (Set.range (u K i))) :
    ∃ D ∈ (psiZ K i).range, D ≠ 0 ∧ ∀ k, D * f k ∈ (psiZ K i).range := by
  classical
  choose d hd hd0 hdf using fun k => exists_den (hf k)
  refine ⟨∏ k, d k, prod_mem fun k _ => hd k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k), mul_comm (d k), mul_assoc]
  exact mul_mem (prod_mem fun l _ => hd l) (hdf k)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
