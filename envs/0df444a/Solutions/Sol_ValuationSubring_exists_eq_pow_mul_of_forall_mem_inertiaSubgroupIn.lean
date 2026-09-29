-- Prove2me | solution 1 for ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0a75064e-22bc-5869-83ae-822ffe39c95a

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn

open scoped Pointwise

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : AlgebraicClosure ℚ) (hcA : c ∈ A) (hc0 : c ≠ 0)
    (hc : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ c = c) :
    ∃ (s : ℕ) (u : AlgebraicClosure ℚ), u ∈ A ∧ u⁻¹ ∈ A ∧ c = ((ℓ : ℕ) : AlgebraicClosure ℚ) ^ s * u := by
  classical
  obtain ⟨O, hSO, hOA, -, hdvr, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn ℓ A hA {c}
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact ⟨hcA, hc⟩)
  haveI := hdvr
  have hcO : c ∈ O := hSO (by simp)
  have hc0' : (⟨c, hcO⟩ : O) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨s, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0' hirr

  refine ⟨s, ((u : O) : AlgebraicClosure ℚ), hOA (u : O).2, ?_, ?_⟩
  · have h1 : ((u : O) : AlgebraicClosure ℚ) * (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact hOA ((u⁻¹ : Oˣ) : O).2
  · have := congrArg (fun z : O => (z : AlgebraicClosure ℚ)) hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast] at this
    rw [this, mul_comm]

end S_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn (solution)
