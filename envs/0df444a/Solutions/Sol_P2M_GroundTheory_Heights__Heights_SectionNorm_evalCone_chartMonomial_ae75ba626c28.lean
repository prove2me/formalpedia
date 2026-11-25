-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:16:00.326484+00:00
-- url     : https://prove2.me/submissions/b08ff977-aeff-4ae6-9042-0c1b273dfcee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionNorm
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.SectionNorm
theorem _root_.solution (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
end GroundTheory.Heights₂.Heights.SectionNorm
