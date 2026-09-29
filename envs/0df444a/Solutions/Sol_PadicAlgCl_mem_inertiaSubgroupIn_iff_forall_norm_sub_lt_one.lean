-- Prove2me | solution 1 for PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f53d4853-6882-5f2a-be3b-b26253f1d377

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one

set_option autoImplicit false

open scoped TensorProduct

open scoped NNReal Pointwise

theorem solution
    (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
      ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  classical
  set A : ValuationSubring (PadicAlgCl p) := padicIntegers p with hA

  have hmax : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ ‖(a : PadicAlgCl p)‖ < 1 := by
    intro a
    rw [ValuationSubring.valuation_lt_one_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one]
    show ‖(a : PadicAlgCl p)‖₊ < 1 ↔ _
    exact Iff.rfl

  have hstab : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ A.decompositionSubgroup ℚ_[p] := by
    intro τ
    rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
    apply SetLike.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hA, mem_padicIntegers_iff,
      mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

  have key : ∀ d : A.decompositionSubgroup ℚ_[p],
      d ∈ A.inertiaSubgroup ℚ_[p] ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖(d : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x - x‖ < 1 := by
    intro d
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    constructor
    · intro hd x hx
      set a : A := ⟨x, (mem_padicIntegers_iff p).2 (by exact_mod_cast hx)⟩ with ha
      have h1 : (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ_[p]) (IsLocalRing.ResidueField A) d)
          (IsLocalRing.residue A a) = IsLocalRing.residue A a := by rw [hd]; rfl
      rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply, ← IsLocalRing.ResidueField.residue_smul] at h1
      have h2 : d • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h1
      rw [hmax] at h2
      exact h2
    · intro h
      apply RingEquiv.ext
      intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      show (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ_[p]) (IsLocalRing.ResidueField A) d)
          (IsLocalRing.residue A a) = IsLocalRing.residue A a
      rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply, ← IsLocalRing.ResidueField.residue_smul]
      refine Ideal.Quotient.eq.mpr ?_
      rw [hmax]
      have hx : ‖(a : PadicAlgCl p)‖ ≤ 1 := by exact_mod_cast (mem_padicIntegers_iff p).1 a.2
      exact h a hx
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (key d).mp hd
  · intro h
    exact ⟨⟨σ, hstab σ⟩, (key ⟨σ, hstab σ⟩).mpr h, rfl⟩

end S_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
end P2MW
export P2MW.S_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one (solution)
