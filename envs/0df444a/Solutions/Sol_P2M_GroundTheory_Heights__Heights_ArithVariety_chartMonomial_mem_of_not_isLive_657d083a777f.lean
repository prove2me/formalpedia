-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:37.601981+00:00
-- url     : https://prove2.me/submissions/5c86266a-de60-48ca-adeb-07ded71cd888

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartMonomialMemOfNotIsLive

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  unfold ArithVariety.IsLive at hc
  push Not at hc
  obtain ⟨k, hk⟩ := hc
  unfold chartMonomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  exact P.ideal.mul_mem_right _ (P.ideal.pow_mem_of_mem hk _ (hd k))
end ArithVariety
end GroundTheory.Heights₂.Heights
