-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:25.174424+00:00
-- url     : https://prove2.me/submissions/8514cce5-945e-4f26-85bd-776dea54f19b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing

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
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFormsAlt
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (k : ι) :
    chartMonomial c (Pi.single k 1) = X ⟨k, c k⟩ := by
  rw [chartMonomial, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
end GroundTheory.Heights₂.Heights.ChartFormsAlt
