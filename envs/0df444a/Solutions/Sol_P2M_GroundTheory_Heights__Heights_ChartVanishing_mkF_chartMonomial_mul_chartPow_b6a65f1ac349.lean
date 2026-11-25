-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_chartMonomial_mul_chartPow_b6a65f1ac349
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:00.36432+00:00
-- url     : https://prove2.me/submissions/23881dd4-7d89-4743-82e5-1f456dd9a6b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_mkF_X_ne_zero_f0798c5f09f9

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
theorem _root_.solution {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ (d k + D.deg k).toNat) := by
  simp only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero P hc k),
    Int.toNat_of_nonneg (hd k)]
end GroundTheory.Heights₂.Heights.ChartVanishing
