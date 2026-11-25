-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:42.358013+00:00
-- url     : https://prove2.me/submissions/81dd608a-05a3-4388-8f5d-79ee85122c7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_apply_dc9bf8315b28

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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch
namespace GroundTheory.Heights₂.Heights.GoodPointBranch
theorem _root_.solution {d : ℕ} {s : ℝ} {v : Fin d → ℂ} (hv : v ∈ ball (0 : Fin d → ℂ) s) :
    consZero d v ∈ ball (0 : Fin (d + 1) → ℂ) s := by
  rw [mem_ball_zero_iff] at hv ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hv
  rw [pi_norm_lt_iff hs]
  intro i
  rw [consZero_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hs
  · simpa using (norm_le_pi_norm v j).trans_lt hv
end GroundTheory.Heights₂.Heights.GoodPointBranch
