-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:57.095689+00:00
-- url     : https://prove2.me/submissions/4f42e0c8-df9a-40b6-a7bd-2303377b4d6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer

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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  simp only [ArithVariety.IsLive, not_forall, not_not] at hc
  obtain ⟨k, hk⟩ := hc
  rw [chartMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hk _ (hd k))
end GroundTheory.Heights₂.Heights.ChartVanishing
