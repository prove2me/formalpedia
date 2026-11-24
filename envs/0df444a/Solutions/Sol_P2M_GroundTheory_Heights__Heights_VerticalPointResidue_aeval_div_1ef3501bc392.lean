-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_aeval_div_1ef3501bc392
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:43.785836+00:00
-- url     : https://prove2.me/submissions/d1e4871d-0139-4466-95c2-8ba0654a2b05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointResidue
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointResidue
theorem _root_.solution {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K') (c : T)
    (G : MRing (fun _ : Unit => T)) (n : ℕ) (hG : IsMultiHomog G (fun _ => n)) :
    aeval (fun p => y p / y ⟨(), c⟩) G = aeval y G * (y ⟨(), c⟩ ^ n)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = n := hG m hm ()
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : (Σ _ : Unit, T), y ⟨(), c⟩ ^ m p = y ⟨(), c⟩ ^ n := by
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_sigma, Fintype.sum_unique]
    rw [← hmd]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv]
end GroundTheory.Heights₂.Heights.VerticalPointResidue
