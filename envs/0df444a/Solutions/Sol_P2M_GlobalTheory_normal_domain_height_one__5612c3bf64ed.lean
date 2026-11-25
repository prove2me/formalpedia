-- Prove2me | solution 1 for P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:01.269165+00:00
-- url     : https://prove2.me/submissions/16dcdd36-f295-45e9-a724-bd71483a0a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_height_eq_one_of_mem_associatedPrimes
import Theorems.Thm_GlobalTheory_injective_of_isLocalizedModule_nonZeroDivisors
import Theorems.Thm_GlobalTheory_finite_heightOneOrd_vw_ne_zero
import Theorems.Thm_GlobalTheory_mem_range_algebraMap_iff_forall_height_eq_one
import Theorems.Thm_GlobalTheory_mem_range_tensor_iff_forall_height_eq_one
import Theorems.Thm_GlobalTheory_exists_unit_smul_eq_iff_heightOneOrd_vw_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
namespace GlobalTheory
namespace normal_domain_height_one
theorem _root_.solution.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (K : Type v) [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      IsDiscreteValuationRing (Localization.AtPrime p) ∧
      ∃ _ : IsDiscreteValuationRing (primeLocalSubalgebra K p),
        ∀ x : K, x ≠ 0 → WithZero.exp (-heightOneOrd_vw p hp x) =
          (IsDiscreteValuationRing.maximalIdeal (primeLocalSubalgebra K p)).valuation K x) ∧
    (∀ x : K, x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module A M] [Module.Projective A M],
      Function.Injective (TensorProduct.mk A K M 1) ∧
      ∀ v : K ⊗[A] M, v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
        ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
          v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M)) ∧
    (∀ x : K, x ≠ 0 → {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite) ∧
    (∀ x y : K, x ≠ 0 → y ≠ 0 →
      (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
        heightOneOrd_vw p hp x = heightOneOrd_vw p hp y) → ∃ u : Aˣ, u • y = x) ∧
    (∀ a : A, a ≠ 0 → ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {a}), p.height = 1) := by
  refine ⟨fun p _ hp => ⟨isDiscreteValuationRing_of_height_eq_one p hp _,
      isDiscreteValuationRing_of_height_eq_one p hp _, fun x hx => ?_⟩,
    mem_range_algebraMap_iff_forall_height_eq_one,
    fun M _ _ _ => ⟨injective_of_isLocalizedModule_nonZeroDivisors _,
      mem_range_tensor_iff_forall_height_eq_one⟩,
    fun _ => finite_heightOneOrd_vw_ne_zero,
    fun _ _ hx hy => (exists_unit_smul_eq_iff_heightOneOrd_vw_eq hx hy).mpr,
    fun _ ha _ => height_eq_one_of_mem_associatedPrimes ha⟩
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [WithZero.exp_neg, ← heightOneOrdHom_eq_exp p hp hx,
    heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p), inv_inv]
end normal_domain_height_one
end GlobalTheory
