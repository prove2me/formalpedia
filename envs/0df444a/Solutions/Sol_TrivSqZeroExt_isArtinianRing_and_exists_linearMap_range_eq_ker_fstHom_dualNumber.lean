-- Prove2me | solution 1 for TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ef2b0915-1eff-5967-8ed7-40eed869dbb4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber

set_option autoImplicit false

open IsLocalRing

namespace DualNumberSmall28

variable (k : Type) [Field k]

theorem mem_maximalIdeal_iff (x : DualNumber k) :
    x ∈ maximalIdeal (DualNumber k) ↔ x.fst = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst,
    isUnit_iff_ne_zero, not_not]

theorem mem_ker_fstHom_iff (x : DualNumber k) :
    x ∈ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ↔ x.fst = 0 := by
  rw [RingHom.mem_ker]; rfl

theorem ker_fstHom_eq :
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom = maximalIdeal (DualNumber k) := by
  ext x; rw [mem_ker_fstHom_iff, mem_maximalIdeal_iff]

theorem eq_inr_of_fst_eq_zero (x : DualNumber k) (hx : x.fst = 0) :
    x = TrivSqZeroExt.inr x.snd := by
  ext <;> simp [hx]

theorem maximalIdeal_mul_maximalIdeal :
    maximalIdeal (DualNumber k) * maximalIdeal (DualNumber k) = ⊥ := by
  rw [eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [mem_maximalIdeal_iff] at hr hs
  rw [Ideal.mem_bot, eq_inr_of_fst_eq_zero k r hr, eq_inr_of_fst_eq_zero k s hs,
    TrivSqZeroExt.inr_mul_inr]

scoped instance : Module.Finite k (DualNumber k) := by
  change Module.Finite k (k × k); infer_instance

theorem isArtinianRing : IsArtinianRing (DualNumber k) :=
  IsArtinianRing.of_finite k (DualNumber k)

noncomputable def mulEps : DualNumber k →ₗ[DualNumber k] DualNumber k :=
  (LinearMap.id : DualNumber k →ₗ[DualNumber k] DualNumber k).smulRight DualNumber.eps

theorem mulEps_apply (x : DualNumber k) : mulEps k x = TrivSqZeroExt.inr x.fst := by
  change x • (DualNumber.eps : DualNumber k) = _
  rw [smul_eq_mul]
  ext
  · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, mul_zero, TrivSqZeroExt.fst_inr]
  · rw [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps, TrivSqZeroExt.snd_inr,
      MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul, mul_one]

theorem mem_ker_mulEps_iff (x : DualNumber k) : x ∈ LinearMap.ker (mulEps k) ↔ x.fst = 0 := by
  rw [LinearMap.mem_ker, mulEps_apply]
  constructor
  · intro h
    have := congrArg TrivSqZeroExt.snd h
    simpa using this
  · intro h
    rw [h, TrivSqZeroExt.inr_zero]

theorem ker_mulEps_eq : LinearMap.ker (mulEps k) = maximalIdeal (DualNumber k) := by
  ext x; rw [mem_ker_mulEps_iff, mem_maximalIdeal_iff]

theorem mem_range_mulEps_iff (x : DualNumber k) :
    x ∈ LinearMap.range (mulEps k) ↔ x.fst = 0 := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [mulEps_apply, TrivSqZeroExt.fst_inr]
  · intro hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [mulEps_apply, TrivSqZeroExt.fst_inl, eq_inr_of_fst_eq_zero k x hx, TrivSqZeroExt.snd_inr]

noncomputable def iota : ResidueField (DualNumber k) →ₗ[DualNumber k] DualNumber k :=
  (maximalIdeal (DualNumber k)).liftQ (mulEps k) (ker_mulEps_eq k).ge

theorem iota_injective : Function.Injective (iota k) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_mulEps_eq k).le

theorem range_iota :
    LinearMap.range (iota k) =
      Submodule.restrictScalars (DualNumber k)
        (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
  have h : LinearMap.range (iota k) = LinearMap.range (mulEps k) :=
    Submodule.range_liftQ (maximalIdeal (DualNumber k)) (mulEps k) (ker_mulEps_eq k).ge
  rw [h]
  ext x
  rw [mem_range_mulEps_iff, Submodule.restrictScalars_mem, mem_ker_fstHom_iff]

theorem residue_comp_algebraMap_bijective :
    Function.Bijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) := by
  refine ⟨RingHom.injective _, ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨x.fst, ?_⟩
  change residue (DualNumber k) (algebraMap k (DualNumber k) x.fst) = residue (DualNumber k) x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff,
    TrivSqZeroExt.algebraMap_eq_inl]
  simp

end DualNumberSmall28
p2m_reactivate "P2MW.S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber.DualNumberSmall28"

open DualNumberSmall28 in
theorem solution
    (k : Type) [Field k] :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    IsArtinianRing (DualNumber k) ∧
    Function.Surjective (algebraMap (DualNumber k) k) ∧
    IsNilpotent (RingHom.ker (algebraMap (DualNumber k) k)) ∧
    RingHom.ker (algebraMap (DualNumber k) k) * maximalIdeal (DualNumber k) = ⊥ ∧
    RingHom.ker (algebraMap (DualNumber k) k) ≤ maximalIdeal (DualNumber k) ∧
    (∃ ι : ResidueField (DualNumber k) →ₗ[DualNumber k] DualNumber k,
      Function.Injective ι ∧
      LinearMap.range ι = Submodule.restrictScalars (DualNumber k) (RingHom.ker (algebraMap (DualNumber k) k))) ∧
    Function.Bijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) ∧
    (IsAlgClosed k → IsAlgClosed (ResidueField (DualNumber k))) := by
  letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
  have halg : algebraMap (DualNumber k) k = (TrivSqZeroExt.fstHom k k k).toRingHom := rfl
  rw [halg]
  refine ⟨isArtinianRing k, ?_, ?_, ?_, ?_, ⟨iota k, iota_injective k, range_iota k⟩,
    residue_comp_algebraMap_bijective k, ?_⟩
  · intro a; exact ⟨TrivSqZeroExt.inl a, TrivSqZeroExt.fst_inl k a⟩
  · rw [ker_fstHom_eq]
    refine ⟨2, ?_⟩
    calc maximalIdeal (DualNumber k) ^ 2
        = maximalIdeal (DualNumber k) * maximalIdeal (DualNumber k) := pow_two _
      _ = ⊥ := maximalIdeal_mul_maximalIdeal k
      _ = 0 := Submodule.zero_eq_bot.symm
  · rw [ker_fstHom_eq, maximalIdeal_mul_maximalIdeal]
  · rw [ker_fstHom_eq]
  · intro hk
    exact IsAlgClosed.of_ringEquiv k (ResidueField (DualNumber k))
      (RingEquiv.ofBijective _ (residue_comp_algebraMap_bijective k))

end S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
end P2MW
export P2MW.S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber (solution)
