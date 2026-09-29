-- Prove2me | solution 1 for PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ad5013b7-70bd-57fa-bbab-63ee34e8ba70

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete

set_option autoImplicit false

noncomputable section

namespace OKDVR

section transport

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mem_smul_top_iff (J : Ideal B) (x : B) : x ∈ (J • ⊤ : Submodule B B) ↔ x ∈ J := by
  change x ∈ J * ⊤ ↔ x ∈ J
  rw [Ideal.mul_top]

theorem sModEq_smul_top_iff (J : Ideal B) (x y : B) : x ≡ y [SMOD (J • ⊤ : Submodule B B)] ↔ x - y ∈ J := by
  rw [SModEq.sub_mem, mem_smul_top_iff]

theorem mem_map_pow_iff (e : A ≃+* B) (I : Ideal A) (n : ℕ) (x : B) :
    x ∈ (I.map (e : A →+* B)) ^ n ↔ e.symm x ∈ I ^ n := by
  rw [← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]

theorem isAdicComplete_map_of_ringEquiv (e : A ≃+* B) (I : Ideal A) [h : IsAdicComplete I A] :
    IsAdicComplete (I.map (e : A →+* B)) B := by
  haveI : IsHausdorff (I.map (e : A →+* B)) B := by
    refine ⟨fun x hx => ?_⟩
    have hx' : ∀ n : ℕ, e.symm x ∈ I ^ n := fun n => by
      have h1 := hx n
      rw [sModEq_smul_top_iff, sub_zero, mem_map_pow_iff] at h1
      exact h1
    have h0 : e.symm x = 0 := IsHausdorff.haus h.toIsHausdorff (e.symm x) fun n => by
      rw [sModEq_smul_top_iff, sub_zero]; exact hx' n
    simpa using congrArg e h0
  haveI : IsPrecomplete (I.map (e : A →+* B)) B := by
    refine ⟨fun {f} hf => ?_⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => e.symm (f n)) fun {m n} hmn => by
      rw [sModEq_smul_top_iff, ← map_sub, ← mem_map_pow_iff]
      have h1 := hf hmn
      rw [sModEq_smul_top_iff] at h1
      exact h1
    refine ⟨e L, fun n => ?_⟩
    rw [sModEq_smul_top_iff, mem_map_pow_iff, map_sub, RingEquiv.symm_apply_apply]
    have h1 := hL n
    rw [sModEq_smul_top_iff] at h1
    exact h1
  exact IsAdicComplete.mk

theorem map_maximalIdeal_of_ringEquiv [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    (IsLocalRing.maximalIdeal A).map (e : A →+* B) = IsLocalRing.maximalIdeal B := by
  ext x
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  refine not_congr ⟨fun hu => ?_, fun hu => ?_⟩
  · simpa using hu.map e
  · exact hu.map e.symm

end transport

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isScalarTower_int_K : IsScalarTower ℤ_[p] K (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isIntegral_coe_iff (x : K) : IsIntegral ℤ_[p] (x : PadicAlgCl p) ↔ IsIntegral ℤ_[p] x :=
  isIntegral_algebraMap_iff (R := ℤ_[p]) (A := K) (B := PadicAlgCl p) Subtype.val_injective

def toIC : PadicAlgCl.ringOfIntegers p K →ₐ[ℤ_[p]] integralClosure ℤ_[p] K where
  toFun x := ⟨⟨(x : PadicAlgCl p), PadicAlgCl.ringOfIntegers.coe_mem x⟩,
    (mem_integralClosure_iff ℤ_[p] K).2
      ((isIntegral_coe_iff p K _).1 (PadicAlgCl.ringOfIntegers.isIntegral_coe x))⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  commutes' _ := Subtype.ext (Subtype.ext rfl)

def ofIC : integralClosure ℤ_[p] K →ₐ[ℤ_[p]] PadicAlgCl.ringOfIntegers p K where
  toFun y := ⟨((y : K) : PadicAlgCl p),
    ⟨(isIntegral_coe_iff p K _).2 ((mem_integralClosure_iff ℤ_[p] K).1 y.2), (y : K).2⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

def equivIC : PadicAlgCl.ringOfIntegers p K ≃ₐ[ℤ_[p]] integralClosure ℤ_[p] K :=
  AlgEquiv.ofAlgHom (toIC p K) (ofIC p K) (AlgHom.ext fun _ => Subtype.ext (Subtype.ext rfl))
    (AlgHom.ext fun _ => Subtype.ext rfl)

theorem natCast_ne_zero : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ≠ 0 := by
  intro h0
  have h1 := congrArg (algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) h0
  rw [map_natCast, map_zero] at h1
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h1

end OKDVR
p2m_reactivate "P2MW.S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete.OKDVR"

open OKDVR in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    Module.Finite ℤ_[p] (PadicAlgCl.ringOfIntegers p K) ∧
    ∃ _ : IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K),
      IsAdicComplete (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K))
        (PadicAlgCl.ringOfIntegers p K) := by

  obtain ⟨hfin, hdvr, hcomp⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[p] ℚ_[p] K
  haveI := hfin
  haveI := hdvr
  haveI := hcomp
  let e := equivIC p K
  let e' : integralClosure ℤ_[p] K ≃+* PadicAlgCl.ringOfIntegers p K := e.symm.toRingEquiv

  have hfinO : Module.Finite ℤ_[p] (PadicAlgCl.ringOfIntegers p K) :=
    Module.Finite.equiv e.symm.toLinearEquiv

  haveI hPIR : IsPrincipalIdealRing (PadicAlgCl.ringOfIntegers p K) :=
    IsPrincipalIdealRing.of_surjective (e' : integralClosure ℤ_[p] K →+* PadicAlgCl.ringOfIntegers p K)
      e'.surjective
  haveI hLR : IsLocalRing (PadicAlgCl.ringOfIntegers p K) :=
    IsLocalRing.of_surjective' (e' : integralClosure ℤ_[p] K →+* PadicAlgCl.ringOfIntegers p K)
      e'.surjective
  have hp : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈
      IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).2 (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  have hnf : IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) ≠ ⊥ := fun hbot => by
    rw [hbot, Ideal.mem_bot] at hp
    exact natCast_ne_zero p K hp
  have hDVR : IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K) :=
    { toIsPrincipalIdealRing := hPIR, toIsLocalRing := hLR, not_a_field' := hnf }

  have hcompO : IsAdicComplete (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K))
      (PadicAlgCl.ringOfIntegers p K) := by
    rw [← map_maximalIdeal_of_ringEquiv e']
    exact isAdicComplete_map_of_ringEquiv e' _
  exact ⟨hfinO, hDVR, hcompO⟩

end
end S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
end P2MW
export P2MW.S_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete (solution)
