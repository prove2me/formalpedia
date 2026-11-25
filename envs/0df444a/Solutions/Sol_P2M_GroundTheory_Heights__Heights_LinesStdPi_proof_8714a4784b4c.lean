-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesStdPi_proof_8714a4784b4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:35:53.283631+00:00
-- url     : https://prove2.me/submissions/d516398e-8193-4a7e-8362-2fc9853a0481

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdPi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19

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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LinesStdPi
theorem _root_.solution : LinesStdPi.Statement := by
  intro K _ k
  ext v
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      dsimp only
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro i; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro i; exact Submodule.add_mem _ (hx i) (hy i)
    | smul a x _ hx => intro i; exact Submodule.smul_mem _ a (hx i)
  · intro hv
    choose y hy using fun i => Submodule.mem_one.mp (hv i)
    have hv' : v = fun i => algebraMap (𝓞 K) K (y i) := funext fun i => (hy i).symm
    rw [hv', KLinesStdPi.eq_sum_smul_single]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end LinesStdPi
end GroundTheory.Heights₂.Heights
