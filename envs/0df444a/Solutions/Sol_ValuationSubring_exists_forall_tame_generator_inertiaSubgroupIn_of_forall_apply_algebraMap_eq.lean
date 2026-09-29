-- Prove2me | solution 1 for ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/16148cf2-061e-5f22-bfaa-2ed578995231

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

section
open scoped Pointwise

namespace C7TameL

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

end C7TameL

end

open scoped Pointwise in
open C7TameL in

theorem solution
    {q : ℕ} (hq' : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q)
    (L : Type) [Field L] [Algebra L (AlgebraicClosure ℚ)] :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      (∀ l : L, γ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ∀ (m : ℕ),
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ →
          (∀ l : L, τ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
            x ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, x (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            w ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, w (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            τ = γ ^ j * x ^ (ℓ ^ m) * w ^ (ℓ ^ m) := by
  classical

  have hinj : Function.Injective (algebraMap L (AlgebraicClosure ℚ)) := (algebraMap L (AlgebraicClosure ℚ)).injective
  haveI : CharZero L := (algebraMap L (AlgebraicClosure ℚ)).charZero
  haveI : IsScalarTower ℚ L (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)), eq_ratCast (algebraMap ℚ L), map_ratCast]
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
    haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
      rw [isAlgClosure_iff]; exact ⟨inferInstance, hQalg⟩
    exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  haveI : IsGalois L (AlgebraicClosure ℚ) := IsGalois.tower_top_of_isGalois (F := ℚ) (K := L) (E := AlgebraicClosure ℚ)
  have halg : ∀ x : AlgebraicClosure ℚ, IsAlgebraic ℚ x := fun x => hQalg.isAlgebraic x

  have hmem : ∀ σ : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn L ↔ σ.restrictScalars ℚ ∈ P.inertiaSubgroupIn ℚ := by
    intro σ
    show σ ∈ (P.inertiaSubgroup L).map (P.decompositionSubgroup L).subtype ↔
      σ.restrictScalars ℚ ∈ (P.inertiaSubgroup ℚ).map (P.decompositionSubgroup ℚ).subtype
    rw [mem_inertia_map_iff, mem_inertia_map_iff]
    have hsmul : σ.restrictScalars ℚ • P = σ • P := by
      ext x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
      rfl
    have hD : σ ∈ P.decompositionSubgroup L ↔ σ.restrictScalars ℚ ∈ P.decompositionSubgroup ℚ := by
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hsmul]
    rw [hD]
    rfl

  have hrmul : ∀ f g : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ,
      (f * g).restrictScalars ℚ = f.restrictScalars ℚ * g.restrictScalars ℚ := fun f g => by ext; rfl
  have hrpow : ∀ (f : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ) (n : ℕ),
      (f ^ n).restrictScalars ℚ = f.restrictScalars ℚ ^ n := by
    intro f n
    induction n with
    | zero => ext; rfl
    | succ n ih => rw [pow_succ, pow_succ, hrmul, ih]

  obtain ⟨γ, hγ, hgen⟩ :=
    ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois (k := L) halg hq' P hq
  refine ⟨γ.restrictScalars ℚ, (hmem γ).mp hγ, fun l => γ.commutes l, ?_⟩
  intro ℓ hℓ hℓq m τ hτ hτL
  let τL : AlgebraicClosure ℚ ≃ₐ[L] AlgebraicClosure ℚ := { τ.toRingEquiv with commutes' := hτL }
  have hτL' : τL.restrictScalars ℚ = τ := by ext x; rfl
  have hτLmem : τL ∈ P.inertiaSubgroupIn L := (hmem τL).mpr (hτL' ▸ hτ)
  obtain ⟨j, x, w, hx, hw, heq⟩ := hgen ℓ hℓ hℓq m τL hτLmem
  refine ⟨j, x.restrictScalars ℚ, w.restrictScalars ℚ, (hmem x).mp hx, fun l => x.commutes l,
    (hmem w).mp hw, fun l => w.commutes l, ?_⟩
  rw [← hτL', heq, hrmul, hrmul, hrpow, hrpow, hrpow]

end S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
end P2MW
export P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq (solution)
