-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pointConeMap_of_homog_d558e640ba56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:31.706994+00:00
-- url     : https://prove2.me/submissions/78c33ec3-ea91-4205-93a0-85049eed78bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (z : (Σ k, ι k) → Φ) {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) :
    pointConeMap O z f = C (aeval z f) * ∏ k, X k ^ b k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : ∀ k, ∑ i : ι k, m ⟨k, i⟩ = b k := by
    intro k
    have h1 := congrFun (hf (mem_support_iff.mp hm)) k
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    rw [← h1, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [blockWeight]
    · intro k' _ hk'
      simp [blockWeight, Ne.symm hk']
    · simp
  simp only [pointConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  have hB : ∏ x : (Σ k, ι k), (X x.1 : MvPolynomial K Φ) ^ m x = ∏ k, X k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X k : MvPolynomial K Φ) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hw k]
  rw [hB, MvPolynomial.algebraMap_apply]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
