-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:19.590918+00:00
-- url     : https://prove2.me/submissions/9c6d885a-e13b-4e35-bfc5-08e72c8155af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
namespace GroundTheory.Heights₂.Heights.FlagTypings
theorem _root_.solution (y : (Σ k, ι k) → Ω) {s : MRingOver R ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) :
    NumbersDVR.pointConeMap R y s = C (aeval y s) * ∏ k, X k ^ a k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [NumbersDVR.pointConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  have hB : ∏ x : (Σ k, ι k), (X x.1 : MvPolynomial K Ω) ^ m x = ∏ k, X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hB, MvPolynomial.algebraMap_apply]
end GroundTheory.Heights₂.Heights.FlagTypings
