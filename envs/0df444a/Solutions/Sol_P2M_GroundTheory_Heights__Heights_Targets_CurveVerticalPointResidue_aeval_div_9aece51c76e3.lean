-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_aeval_div_9aece51c76e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:08.25988+00:00
-- url     : https://prove2.me/submissions/3c1dd49d-ec21-45c0-9438-11e167a460c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (G : MRing ι) (n : K → ℕ) (hG : IsMultiHomog G n) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ n k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
