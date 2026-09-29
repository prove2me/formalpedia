-- Prove2me | solution 1 for PadicAlgCl.mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/91b437ae-04b6-5625-bebf-6ac7b5d91b82

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
    [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]
    (x : PadicAlgCl p)
    (hx : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, τ x = x) :
    x ∈ Set.range (algebraMap K' (PadicAlgCl p)) := by

  have hxK : x ∈ K := by
    have hfix : x ∈ IntermediateField.fixedField K.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact hx (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ)
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at hfix

  obtain ⟨m, y, hy⟩ := PadicAlgCl.ringOfIntegers.exists_pow_natCast_mul_mem p K hxK
  have hp0 : ((p : PadicAlgCl p) ^ m) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hOy : algebraMap K' (PadicAlgCl p) (algebraMap (PadicAlgCl.ringOfIntegers p K) K' y) =
      (y : PadicAlgCl p) :=
    (IsScalarTower.algebraMap_apply (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p) y).symm
  have hOp : algebraMap K' (PadicAlgCl p)
      (algebraMap (PadicAlgCl.ringOfIntegers p K) K' (((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m)) =
      (p : PadicAlgCl p) ^ m := by
    rw [← IsScalarTower.algebraMap_apply (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p), map_pow,
      map_natCast]
  refine ⟨algebraMap (PadicAlgCl.ringOfIntegers p K) K' y /
      algebraMap (PadicAlgCl.ringOfIntegers p K) K' (((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m), ?_⟩
  rw [map_div₀, hOy, hOp, hy, mul_div_assoc, mul_div_cancel₀ _ hp0]

end S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
end P2MW
export P2MW.S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq (solution)
