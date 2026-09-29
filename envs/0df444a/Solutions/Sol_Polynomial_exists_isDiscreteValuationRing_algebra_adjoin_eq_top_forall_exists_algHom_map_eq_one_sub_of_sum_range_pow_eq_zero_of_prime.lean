-- Prove2me | solution 1 for Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fabaf5ca-293b-55a3-b100-e3f60a1e1d58

import Mathlib
import Theorems.Thm_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (q : ℕ) [Fact q.Prime]
    (Z₀ : Type) [CommRing Z₀] [IsDomain Z₀] [IsDiscreteValuationRing Z₀]
    (hZ₀ : maximalIdeal Z₀ = Ideal.span {(q : Z₀)}) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra Z₀ V)
      (_ : Module.Finite Z₀ V) (_ : Module.Free Z₀ V)
      (_ : Finite (ResidueField Z₀) → Finite (ResidueField V))
      (ϖ : V) (_ : maximalIdeal V = Ideal.span {ϖ}) (_ : Algebra.adjoin Z₀ {ϖ} = ⊤)
      (ε : V) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : V))
      (_ : ∑ i ∈ Finset.range q, (1 - ϖ) ^ i = 0),
      ∀ (R : Type) [CommRing R] [Algebra Z₀ R] (ζ : R), ∑ i ∈ Finset.range q, ζ ^ i = 0 →
        ∃ ι : V →ₐ[Z₀] R, ι ϖ = 1 - ζ := by
  classical
  by_cases hq : 3 ≤ q
  · exact Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero q hq Z₀ hZ₀
  ·
    have hq2 : q = 2 := by
      have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
      omega
    subst hq2
    refine ⟨Z₀, inferInstance, inferInstance, inferInstance, Algebra.id Z₀, inferInstance, inferInstance, fun h => h,
      (2 : Z₀), by exact_mod_cast hZ₀, ?_, 1, isUnit_one, by norm_num, by norm_num, ?_⟩
    · exact Algebra.eq_top_iff.mpr (fun x => by simpa using Subalgebra.algebraMap_mem (Algebra.adjoin Z₀ {(2 : Z₀)}) x)
    · intro R _ _ ζ hζ
      refine ⟨Algebra.ofId Z₀ R, ?_⟩
      have h : (1 : R) + ζ = 0 := by simpa [Finset.sum_range_succ] using hζ
      rw [Algebra.ofId_apply, map_ofNat]
      linear_combination h

end S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime
end P2MW
export P2MW.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero_of_prime (solution)
