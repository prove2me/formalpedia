-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:16.862099+00:00
-- url     : https://prove2.me/submissions/70ab2c67-efe6-4d03-8d87-595016ec5b92

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
theorem _root_.solution (N : ℕ) (u : Fin 1 × Fin N → ℂ) :
    (fun j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)) =
      ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ)⁻¹ • firstRow N u := by
  ext j
  simp [sphereNormalize, HermNorm.std_norm_eq, firstRow_apply]
end GroundTheory.Heights₂.Heights.SphereLawBasic
