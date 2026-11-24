-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_div_chart_a79e2c68e520
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:55.559565+00:00
-- url     : https://prove2.me/submissions/4a7819b2-364b-4ec2-9bb6-5f336d8a34ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) G = aeval z G * ∏ k, (z ⟨k, c k⟩ ^ d k)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmd : ∀ k, ∑ i, m ⟨k, i⟩ = d k := (geoMultiHomog_iff G d).mpr hG m hm
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : Coord n, z ⟨p.1, c p.1⟩ ^ m p = ∏ k, z ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← hmd k, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv, Finset.prod_inv_distrib]
end GroundTheory.Heights₂.Heights
