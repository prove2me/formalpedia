-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_mem_orbitIdeal_of_homog_7800250f67a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:51.760953+00:00
-- url     : https://prove2.me/submissions/67eced11-f56b-4159-b66d-d07b3df0c0b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) {f : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f d) (h0 : aeval (flatCone x) f = 0) :
    f ∈ orbitIdeal x := by
  have hf' := (geoMultiHomog_iff f d).mpr hf
  have key : Geo.mConeMap (ι := blockIdx n) (flatCone x) f =
      C (aeval (flatCone x) f) * ∏ k, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ d k := by
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p =
        ∏ k, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ d k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
    simp only [Geo.mConeMap, aeval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
      MvPolynomial.algebraMap_apply]
    ac_rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, key, h0, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.OrbitConjSum
