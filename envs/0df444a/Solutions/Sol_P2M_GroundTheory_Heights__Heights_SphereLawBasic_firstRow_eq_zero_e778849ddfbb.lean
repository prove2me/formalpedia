-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_eq_zero_e778849ddfbb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:22.692738+00:00
-- url     : https://prove2.me/submissions/0662ac7f-df3b-4306-aaff-d0633801a4cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_firstRow_apply_5143842c4916

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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic
namespace GroundTheory.Heights₂.Heights.SphereLawBasic
theorem _root_.solution (N : ℕ) (u : Fin 1 × Fin N → ℂ) (h : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0) :
    firstRow N u = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖u (0, i)‖)).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
  ext j
  simpa [firstRow_apply] using h' j (Finset.mem_univ j)
end GroundTheory.Heights₂.Heights.SphereLawBasic
