-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_chartMonomial_mul_chartPow_10a98fec4d52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:54.329738+00:00
-- url     : https://prove2.me/submissions/39e21ddd-a871-4f6e-a837-633d047332b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mkF_X_ne_zero_6e1224960199

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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by
  simp only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero hc k), Int.toNat_of_nonneg (hd k)]
end GroundTheory.Heights₂.Heights.SectionCycle
