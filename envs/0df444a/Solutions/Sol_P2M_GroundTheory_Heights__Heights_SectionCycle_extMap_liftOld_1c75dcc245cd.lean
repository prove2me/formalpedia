-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:35.818126+00:00
-- url     : https://prove2.me/submissions/7107cb4c-9882-4f4d-a5d1-4cb6eee50934

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_monomial_3eda3bb7f3ac

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
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {h : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hh : IsWeightedHomogeneous (coordDeg n) h δ) :
    D.extMap (D.liftOld h) = C (P.mkF h) * ∏ k, X (some k) ^ δ k := by
  rw [h.as_sum, map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [extMap_liftOld_monomial, hh (mem_support_iff.mp hs)]
end GroundTheory.Heights₂.Heights.SectionCycle
