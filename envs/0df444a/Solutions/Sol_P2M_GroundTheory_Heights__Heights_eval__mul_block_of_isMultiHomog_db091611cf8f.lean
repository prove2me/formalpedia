-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:56.723961+00:00
-- url     : https://prove2.me/submissions/6cd492ff-975d-4f26-9fa8-c5765a391439

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm

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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by
  classical
  simp only [eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
  rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
end GroundTheory.Heights₂.Heights
