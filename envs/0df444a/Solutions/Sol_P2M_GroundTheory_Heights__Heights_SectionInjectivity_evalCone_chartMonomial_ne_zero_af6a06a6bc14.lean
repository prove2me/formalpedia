-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:26.731797+00:00
-- url     : https://prove2.me/submissions/d54e550d-5300-4180-81f0-4e50c8d5e528

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore

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
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.SectionInjectivity
theorem _root_.solution {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
end GroundTheory.Heights₂.Heights.SectionInjectivity
