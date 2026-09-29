-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/98247f7d-c2d2-5a6d-a68b-0fef13731e9f

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Compactness.Compact
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq

set_option autoImplicit false

namespace CycloInertiaSurj

open scoped Pointwise IntermediateField

section General

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ σ • A = A := MulAction.mem_stabilizer_iff

theorem residue_eq_iff (A : ValuationSubring L) (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ ((a : L) - b) ∈ A.nonunits := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (τ : L ≃ₐ[K] L) :
    τ ∈ A.inertiaSubgroupIn K ↔ τ • A = A ∧ ∀ a ∈ A, τ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(mem_decompositionSubgroup_iff A _).1 d.2, fun a ha => ?_⟩
    have hker : ∀ x : IsLocalRing.ResidueField A, d • x = x := fun x => by
      have := RingEquiv.congr_fun (MonoidHom.mem_ker.1 hd) x
      simpa using this
    have h1 := hker (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff] at h1
    simp at h1
    exact h1
  · rintro ⟨hτ, h⟩
    have hτ' : τ ∈ A.decompositionSubgroup K := (mem_decompositionSubgroup_iff A τ).2 hτ
    refine ⟨⟨τ, hτ'⟩, ?_, rfl⟩
    simp only [ValuationSubring.inertiaSubgroup, SetLike.mem_coe, MonoidHom.mem_ker]
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨τ, hτ'⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff]
    exact h a a.2

theorem mem_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ g • A ↔ g⁻¹ x ∈ A :=
  ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem isOpen_of_mul_fixingSubgroup_mem (T : Set (L ≃ₐ[K] L)) (E : IntermediateField K L)
    [FiniteDimensional K E]
    (h : ∀ σ ∈ T, ∀ τ ∈ E.fixingSubgroup, σ * τ ∈ T) : IsOpen T := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, E.fixingSubgroup_isOpen.leftCoset σ, ?_⟩
  · intro x hx
    rw [mem_leftCoset_iff] at hx
    have := h σ hσ (σ⁻¹ * x) hx
    rwa [mul_inv_cancel_left] at this
  · rw [mem_leftCoset_iff, inv_mul_cancel]
    exact E.fixingSubgroup.one_mem

theorem isClopen_setOf_apply_eq {x : L} (hx : IsIntegral K x) (y : L) :
    IsClopen {σ : L ≃ₐ[K] L | σ x = y} := by
  haveI : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have hxE : x ∈ K⟮x⟯ := IntermediateField.mem_adjoin_simple_self K x
  have key : ∀ σ τ : L ≃ₐ[K] L, τ ∈ (K⟮x⟯).fixingSubgroup → (σ * τ) x = σ x := by
    intro σ τ hτ
    rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x hxE]
  constructor
  · rw [← isOpen_compl_iff]
    refine isOpen_of_mul_fixingSubgroup_mem _ K⟮x⟯ fun σ hσ τ hτ => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hσ ⊢
    rwa [key σ τ hτ]
  · refine isOpen_of_mul_fixingSubgroup_mem _ K⟮x⟯ fun σ hσ τ hτ => ?_
    simp only [Set.mem_setOf_eq] at hσ ⊢
    rwa [key σ τ hτ]

theorem isClosed_inertiaSubgroupIn [Algebra.IsAlgebraic K L] (A : ValuationSubring L) :
    IsClosed (A.inertiaSubgroupIn K : Set (L ≃ₐ[K] L)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  rw [Set.mem_compl_iff, SetLike.mem_coe, mem_inertiaSubgroupIn_iff, not_and_or] at hσ
  rcases hσ with hdec | hres
  ·
    have hx : ∃ x : L, ¬ (x ∈ σ • A ↔ x ∈ A) :=
      not_forall.mp fun hall => hdec (SetLike.ext hall)
    obtain ⟨x, hx⟩ := hx
    rw [mem_smul_iff] at hx
    refine ⟨{τ : L ≃ₐ[K] L | τ (σ⁻¹ x) = x}, ?_,
      (isClopen_setOf_apply_eq (Algebra.IsIntegral.isIntegral (σ⁻¹ x)) x).isOpen, ?_⟩
    · intro τ hτ hτI
      rw [SetLike.mem_coe, mem_inertiaSubgroupIn_iff] at hτI
      have hτx : τ⁻¹ x = σ⁻¹ x := by
        have h1 : τ (σ⁻¹ x) = x := hτ
        rw [← h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply, h1]
      apply hx
      rw [← hτx, ← mem_smul_iff, hτI.1]
    · show σ (σ⁻¹ x) = x
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  ·
    obtain ⟨a, ha'⟩ := not_forall.mp hres
    obtain ⟨haA, ha⟩ := Classical.not_imp.mp ha'
    refine ⟨{τ : L ≃ₐ[K] L | τ a = σ a}, ?_,
      (isClopen_setOf_apply_eq (Algebra.IsIntegral.isIntegral a) (σ a)).isOpen, rfl⟩
    intro τ hτ hτI
    rw [SetLike.mem_coe, mem_inertiaSubgroupIn_iff] at hτI
    have h1 : τ a = σ a := hτ
    exact ha (h1 ▸ hτI.2 a haA)

end General

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem pow_val_toZModPow_eq {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) {m n : ℕ} (hmn : m ≤ n)
    {M : Type*} [Monoid M] {ζ : M} (hζ : ζ ^ p ^ m = 1) :
    ζ ^ (PadicInt.toZModPow n u).val = ζ ^ (PadicInt.toZModPow m u).val := by
  rw [pow_eq_pow_mod _ hζ]
  congr 1
  rw [← PadicInt.cast_toZModPow m n hmn u, ZMod.cast_eq_val, ZMod.val_natCast]

end CycloInertiaSurj

open CycloInertiaSurj in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} [Fact p.Prime] (hA : A.LiesOverPrime p)
    (u : ℤ_[p]ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ,
      cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv = u := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.ne_zero⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsGalois.mk
  haveI hE : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i => inferInstance

  let c : ℕ → ℕ := fun k => (PadicInt.toZModPow k (u : ℤ_[p])).val
  let F : ℕ → Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := fun k =>
    (A.inertiaSubgroupIn ℚ : Set _) ∩
      ⋂ (ζ : AlgebraicClosure ℚ) (_ : ζ ^ p ^ k = 1), {σ | σ ζ = ζ ^ c k}
  have hFmem : ∀ k σ, σ ∈ F k ↔ σ ∈ A.inertiaSubgroupIn ℚ ∧
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ k = 1 → σ ζ = ζ ^ c k := by
    intro k σ
    simp only [F, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]

  have hne : ∀ k, (F k).Nonempty := by
    intro k
    obtain ⟨σ, hσI, hσ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one A hp hA k
        (Units.map (PadicInt.toZModPow k).toMonoidHom u)
    exact ⟨σ, (hFmem k σ).2 ⟨hσI, fun ζ hζ => hσ ζ hζ⟩⟩

  have hmono : ∀ k, F (k + 1) ⊆ F k := by
    intro k σ hσ
    rw [hFmem] at hσ ⊢
    refine ⟨hσ.1, fun ζ hζ => ?_⟩
    have hζ' : ζ ^ p ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, hζ, one_pow]
    rw [hσ.2 ζ hζ']
    exact pow_val_toZModPow_eq (u : ℤ_[p]) (Nat.le_succ k) hζ

  have hclosed : ∀ k, IsClosed (F k) := by
    intro k
    refine (isClosed_inertiaSubgroupIn A).inter (isClosed_iInter fun ζ => isClosed_iInter fun _ => ?_)
    exact (isClopen_setOf_apply_eq (Algebra.IsIntegral.isIntegral ζ) _).isClosed

  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne
    (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, ((hFmem 0 σ).1 (hσ 0)).1, ?_⟩

  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζ1 : ζ ^ p ^ n = 1 := hζ.pow_eq_one
  have h1 : σ ζ = ζ ^ ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val.toZModPow n).val :=
    cyclotomicCharacter.spec p σ.toRingEquiv ζ hζ1
  have h2 : σ ζ = ζ ^ c n := ((hFmem n σ).1 (hσ n)).2 ζ hζ1
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2)

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq (solution)
