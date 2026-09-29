-- Prove2me | solution 1 for RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cb7204fe-77f6-5cd3-98c3-e2648f8bbe31

import Theorems.Thm_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Theorems.Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
import Definitions.Def_GaloisRep_Flat
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_GaloisRep_Adic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FreeModule.PID
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option Elab.async false

open IsLocalRing

namespace W5bT

local notation "Gℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section R0

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

noncomputable def R0 : Subring 𝒪 :=
  ((⊥ : Subfield (ResidueField 𝒪)).toSubring).comap (residue 𝒪)

variable {𝒪}

theorem mem_R0_iff {x : 𝒪} :
    x ∈ R0 𝒪 ↔ residue 𝒪 x ∈ (⊥ : Subfield (ResidueField 𝒪)) := Iff.rfl

theorem mem_R0_of_mem_maximalIdeal {x : 𝒪} (hx : x ∈ maximalIdeal 𝒪) : x ∈ R0 𝒪 := by
  rw [mem_R0_iff, (residue_eq_zero_iff x).mpr hx]
  exact zero_mem _

theorem isUnit_of_not_mem {x : R0 𝒪} (hx : (x : 𝒪) ∉ maximalIdeal 𝒪) : IsUnit x := by
  have hu : IsUnit (x : 𝒪) := by
    by_contra h
    exact hx ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu'⟩ := hu
  have hinv : (↑u⁻¹ : 𝒪) ∈ R0 𝒪 := by
    rw [mem_R0_iff, map_units_inv (residue 𝒪) u]
    refine (⊥ : Subfield (ResidueField 𝒪)).inv_mem ?_
    rw [hu']
    exact x.2
  refine ⟨⟨x, ⟨↑u⁻¹, hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show (x : 𝒪) * ↑u⁻¹ = 1
    rw [← hu', Units.mul_inv]
  · show (↑u⁻¹ : 𝒪) * x = 1
    rw [← hu', Units.inv_mul]

scoped instance isLocalRing_R0 : IsLocalRing (R0 𝒪) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  by_cases hx : (x : 𝒪) ∈ maximalIdeal 𝒪
  · refine Or.inr (isUnit_of_not_mem fun h1 => ?_)
    have h : (x : 𝒪) + (1 - (x : 𝒪)) ∈ maximalIdeal 𝒪 := add_mem hx h1
    rw [add_sub_cancel] at h
    exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · exact Or.inl (isUnit_of_not_mem hx)

theorem mem_maximalIdeal_R0_iff (x : R0 𝒪) :
    x ∈ maximalIdeal (R0 𝒪) ↔ (x : 𝒪) ∈ maximalIdeal 𝒪 := by
  constructor
  · intro hx
    by_contra h
    exact ((mem_maximalIdeal _).mp hx) (isUnit_of_not_mem h)
  · intro hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact ((mem_maximalIdeal _).mp hx) (hu.map (R0 𝒪).subtype)

noncomputable def resR0 : R0 𝒪 →+* (⊥ : Subfield (ResidueField 𝒪)) :=
  ((residue 𝒪).comp (R0 𝒪).subtype).codRestrict _ (fun x => x.2)

theorem resR0_surjective : Function.Surjective (resR0 (𝒪 := 𝒪)) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ := residue_surjective z
  exact ⟨⟨y, hz⟩, rfl⟩

theorem ker_resR0 : RingHom.ker (resR0 (𝒪 := 𝒪)) = maximalIdeal (R0 𝒪) := by
  ext x
  rw [RingHom.mem_ker, mem_maximalIdeal_R0_iff, ← residue_eq_zero_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem card_residueField_R0 (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] :
    Nat.card (ResidueField (R0 𝒪)) = p := by
  have e1 : ResidueField (R0 𝒪) ≃+* (R0 𝒪 ⧸ RingHom.ker (resR0 (𝒪 := 𝒪))) :=
    Ideal.quotEquivOfEq (ker_resR0 (𝒪 := 𝒪)).symm
  have e2 : (R0 𝒪 ⧸ RingHom.ker (resR0 (𝒪 := 𝒪))) ≃+* (⊥ : Subfield (ResidueField 𝒪)) :=
    RingHom.quotientKerEquivOfSurjective (resR0_surjective (𝒪 := 𝒪))
  rw [Nat.card_congr (e1.trans e2).toEquiv]
  exact Subfield.card_bot (ResidueField 𝒪) p

end R0

section Tame

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField 𝒪) p]

theorem residue_eq_one_of_pow (η : Gℚ →* 𝒪ˣ) {w : Gℚ} {a : ℕ}
    (h : ((η (w ^ p ^ a) : 𝒪ˣ) : 𝒪) - 1 ∈ maximalIdeal 𝒪) :
    residue 𝒪 (η w : 𝒪) = 1 := by
  have h1 : residue 𝒪 (((η w : 𝒪ˣ) : 𝒪) ^ p ^ a - 1) = 0 := by
    rw [residue_eq_zero_iff]
    simpa only [map_pow, Units.val_pow_eq_pow_val] using h
  rw [map_sub, map_pow, map_one] at h1
  have h2 : (residue 𝒪 (η w : 𝒪) - 1) ^ p ^ a = 0 := by
    rw [sub_pow_char_pow, one_pow, h1]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero a (Fact.out : p.Prime).ne_zero)).mp h2)

theorem eta_mem_R0_of_mem_inertia (η : Gℚ →* 𝒪ˣ)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Gℚ, (∀ x ∈ L, σ x = x) → ((η σ : 𝒪ˣ) : 𝒪) - 1 ∈ maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {τ : Gℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) : ((η τ : 𝒪ˣ) : 𝒪) ∈ R0 𝒪 := by
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
    (Fact.out : p.Prime) P hP
  obtain ⟨-, hwild⟩ := hφ τ hτ
  obtain ⟨L, hLfin, hL⟩ := hcont
  haveI := hLfin
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)
  haveI : Normal ℚ F := normalClosure.normal ℚ L (AlgebraicClosure ℚ)
  have hLF : L ≤ F := IntermediateField.le_normalClosure L
  obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild
    (Fact.out : p.Prime) P hP hwild F
  have hres1 : residue 𝒪 (η (φ * τ * φ⁻¹ * (τ ^ p)⁻¹) : 𝒪) = 1 :=
    residue_eq_one_of_pow p η (hL _ (fun x hx => ha x (hLF hx)))
  have hconjη : η (φ * τ * φ⁻¹) = η τ := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hη : η τ = η (φ * τ * φ⁻¹ * (τ ^ p)⁻¹) * η τ ^ p := by
    calc η τ = η (φ * τ * φ⁻¹) := hconjη.symm
      _ = η (φ * τ * φ⁻¹ * (τ ^ p)⁻¹ * τ ^ p) := by rw [inv_mul_cancel_right]
      _ = η (φ * τ * φ⁻¹ * (τ ^ p)⁻¹) * η τ ^ p := by rw [map_mul, map_pow]
  have hr : residue 𝒪 (η τ : 𝒪) ^ p = residue 𝒪 (η τ : 𝒪) := by
    have key : ((η τ : 𝒪ˣ) : 𝒪) =
        ((η (φ * τ * φ⁻¹ * (τ ^ p)⁻¹) : 𝒪ˣ) : 𝒪) * ((η τ : 𝒪ˣ) : 𝒪) ^ p := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      exact congrArg Units.val hη
    have h := congrArg (residue 𝒪) key
    rw [map_mul (residue 𝒪), map_pow (residue 𝒪), hres1, one_mul] at h
    exact h.symm
  exact (Subfield.mem_bot_iff_pow_eq_self (ResidueField 𝒪) p).mpr hr

theorem repr_mem_of_mem_smul_top {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (I : Ideal R) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) (i : ι) :
    b.repr x i ∈ I := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hr
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

theorem hcont_of_basis {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (b : Module.Basis (Fin 2) A ρ.V) (η : Gℚ →* Aˣ)
    (hη : ∀ σ : Gℚ, ρ.ρ σ (b 0) = ((η σ : Aˣ) : A) • b 0) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Gℚ, (∀ x ∈ L, σ x = x) → ((η σ : Aˣ) : A) - 1 ∈ maximalIdeal A := by
  obtain ⟨L, hL, h⟩ := ρ.isAdicContinuous 1
  refine ⟨L, hL, fun σ hσ => ?_⟩
  have hv : (((η σ : Aˣ) : A) - 1) • b 0 ∈ maximalIdeal A • (⊤ : Submodule A ρ.V) := by
    rw [sub_smul, one_smul, ← hη]
    simpa only [pow_one] using h σ hσ (b 0)
  have := repr_mem_of_mem_smul_top b _ hv 0
  rwa [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at this

end Tame

section ApplyW4

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField 𝒪) p]

theorem level_quadratic (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hp𝔪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (η : Gℚ →* 𝒪ˣ) (htame : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ((η σ : 𝒪ˣ) : 𝒪) ∈ R0 𝒪)
    (k : ℕ)
    (N : Type) [AddCommGroup N] [Module 𝒪 N] [DistribMulAction Gℚ N]
    (n₀ : N) (hgen : ∀ n : N, ∃ x : 𝒪, n = x • n₀)
    (hann : ∀ x : 𝒪, x • n₀ = 0 ↔ x ∈ maximalIdeal 𝒪 ^ k)
    (hact : ∀ (σ : Gℚ) (n : N), σ • n = ((η σ : 𝒪ˣ) : 𝒪) • n)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : Gℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f)
    {σ : Gℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (a : ℕ)
    (hσa : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 → σ μ = μ ^ a) :
    (((η σ : 𝒪ˣ) : 𝒪) - a) * (((η σ : 𝒪ˣ) : 𝒪) - 1) ∈ maximalIdeal 𝒪 ^ k := by
  classical

  have hunit : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      ∃ v : (R0 𝒪)ˣ, ((v : R0 𝒪) : 𝒪) = ((η τ : 𝒪ˣ) : 𝒪) := by
    intro τ hτ
    have h1 : ((η τ : 𝒪ˣ) : 𝒪) ∈ R0 𝒪 := htame τ hτ
    have h2 : ((η τ⁻¹ : 𝒪ˣ) : 𝒪) ∈ R0 𝒪 := htame τ⁻¹ (inv_mem hτ)
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · show ((η τ : 𝒪ˣ) : 𝒪) * ((η τ⁻¹ : 𝒪ˣ) : 𝒪) = 1
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · show ((η τ⁻¹ : 𝒪ˣ) : 𝒪) * ((η τ : 𝒪ˣ) : 𝒪) = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  choose! u hu' using hunit
  have hu : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ m : N, τ • m = (u τ : R0 𝒪) • m := by
    intro τ hτ m
    rw [hact]
    show ((η τ : 𝒪ˣ) : 𝒪) • m = ((u τ : R0 𝒪) : 𝒪) • m
    rw [hu' τ hτ]
  have hR : Nat.card (ResidueField (R0 𝒪)) = p := card_residueField_R0 p
  obtain ⟨T, -, hT2, hT3⟩ :=
    FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic p P hP H e he_add he_act
      (R0 𝒪) hR u hu

  have ht₀ : (((η σ : 𝒪ˣ) : 𝒪) - 1) • n₀ ∈ T := by
    have e1 : (((η σ : 𝒪ˣ) : 𝒪) - 1) • n₀ = σ • n₀ - n₀ := by
      rw [sub_smul, one_smul, hact]
    rw [e1]
    exact hT2 σ hσ n₀

  have hpk : ((p ^ k : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 ^ k := by
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow hp𝔪 k
  have hkill : ∀ t ∈ T, p ^ k • t = 0 := by
    intro t _
    obtain ⟨x, rfl⟩ := hgen t
    rw [← Nat.cast_smul_eq_nsmul 𝒪, smul_smul]
    exact (hann _).mpr (Ideal.mul_mem_right _ _ hpk)
  have hfix := hT3 k a σ hσ hσa hkill _ ht₀
  rw [hact, smul_smul, ← Nat.cast_smul_eq_nsmul 𝒪, smul_smul, ← sub_eq_zero, ← sub_smul,
    ← sub_mul] at hfix
  exact (hann _).mp hfix

theorem charP_residueField_of_mem {A : Type} [CommRing A] [IsLocalRing A] {q : ℕ} [Fact q.Prime]
    (hq : (q : A) ∈ maximalIdeal A) : CharP (ResidueField A) q :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr
    (by rw [← map_natCast (residue A), residue_eq_zero_iff]; exact hq)

theorem level_quadratic_of_basis (ρ : GaloisRepAdic 𝒪) (b : Module.Basis (Fin 2) 𝒪 ρ.V)
    (η : Gℚ →* 𝒪ˣ) (hη : ∀ σ : Gℚ, ρ.ρ σ (b 0) = ((η σ : 𝒪ˣ) : 𝒪) • b 0)
    (hp𝔪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (k : ℕ)
    (N : Type) [AddCommGroup N] [Module 𝒪 N] [DistribMulAction Gℚ N]
    (n₀ : N) (hgen : ∀ n : N, ∃ x : 𝒪, n = x • n₀)
    (hann : ∀ x : 𝒪, x • n₀ = 0 ↔ x ∈ maximalIdeal 𝒪 ^ k)
    (hact : ∀ (σ : Gℚ) (n : N), σ • n = ((η σ : 𝒪ˣ) : 𝒪) • n)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : Gℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f)
    {σ : Gℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (a : ℕ)
    (hσa : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 → σ μ = μ ^ a) :
    (((η σ : 𝒪ˣ) : 𝒪) - a) * (((η σ : 𝒪ˣ) : 𝒪) - 1) ∈ maximalIdeal 𝒪 ^ k :=
  level_quadratic p P hP hp𝔪 η
    (fun _ hτ => eta_mem_R0_of_mem_inertia p η (hcont_of_basis ρ b η hη) P hP hτ)
    k N n₀ hgen hann hact H e he_add he_act hσ a hσa

end ApplyW4

end W5bT
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

namespace W5bX

open scoped TensorProduct

local notation "Gℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Transport

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
  {V : Type} [AddCommGroup V] [Module R V]

theorem baseChange_apply_eq_self_of_apply_eq_self (f : V →ₗ[R] V) (v₀ : V) (hfix : f v₀ = v₀)
    (W : Submodule K (K ⊗[R] V)) (hW : W = K ∙ ((1 : K) ⊗ₜ[R] v₀)) :
    ∀ w ∈ W, f.baseChange K w = w := by
  intro w hw
  rw [hW, Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  rw [map_smul, LinearMap.baseChange_tmul, hfix]

theorem baseChange_apply_sub_mem_of_sub_mem_span (f : V →ₗ[R] V) (v₀ : V)
    (hdisp : ∀ v : V, f v - v ∈ Submodule.span R {v₀})
    (W : Submodule K (K ⊗[R] V)) (hW : W = K ∙ ((1 : K) ⊗ₜ[R] v₀)) :
    ∀ x : K ⊗[R] V, f.baseChange K x - x ∈ W := by
  have hv₀ : (1 : K) ⊗ₜ[R] v₀ ∈ W := by
    rw [hW]
    exact Submodule.mem_span_singleton_self _
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, sub_zero]
    exact W.zero_mem
  | tmul c v =>
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hdisp v)
    rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub, ← hr, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    have h1 : (r • c) ⊗ₜ[R] v₀ = (r • c) • ((1 : K) ⊗ₜ[R] v₀) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1]
    exact W.smul_mem _ hv₀
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact W.add_mem hx hy

end Transport
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

section Bridge

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem mem_span_of_repr_one_eq_zero (b : Module.Basis (Fin 2) R V) (u : V)
    (hu : b.repr u 1 = 0) : u ∈ Submodule.span R {b 0} := by
  refine Submodule.mem_span_singleton.mpr ⟨b.repr u 0, ?_⟩
  have h := b.sum_repr u
  rw [Fin.sum_univ_two, hu, zero_smul, add_zero] at h
  exact h

theorem sub_mem_span_of_triangular (b : Module.Basis (Fin 2) R V) (f : V →ₗ[R] V)
    (h0 : b.repr (f (b 0)) 1 = 0) (h1 : b.repr (f (b 1)) 1 = 1) :
    ∀ v : V, f v - v ∈ Submodule.span R {b 0} := by
  intro v
  have hv : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    have h := b.sum_repr v
    rw [Fin.sum_univ_two] at h
    exact h.symm
  have hfv : f v = b.repr v 0 • f (b 0) + b.repr v 1 • f (b 1) := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  have hcoord : b.repr (f v - v) 1 = 0 := by
    rw [map_sub, Finsupp.sub_apply, hfv, map_add, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, h0, h1, smul_zero, zero_add, smul_eq_mul, mul_one,
      sub_self]
  exact mem_span_of_repr_one_eq_zero b _ hcoord

end Bridge
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

section Wrappers

variable {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪'] {K : Type} [Field K] [Algebra 𝒪' K]

theorem disjunct_one (ρ : GaloisRepAdic 𝒪') (b : Module.Basis (Fin 2) 𝒪' ρ.V)
    (η : Gℚ →* 𝒪'ˣ) (hη : ∀ σ : Gℚ, ρ.ρ σ (b 0) = ((η σ : 𝒪'ˣ) : 𝒪') • b 0)
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : W = K ∙ ((1 : K) ⊗ₜ[𝒪'] b 0))
    {σ : Gℚ} (h : η σ = 1) : ∀ w ∈ W, (ρ.ρ σ).baseChange K w = w :=
  baseChange_apply_eq_self_of_apply_eq_self (ρ.ρ σ) (b 0)
    (by rw [hη, h, Units.val_one, one_smul]) W hW

theorem disjunct_two (ρ : GaloisRepAdic 𝒪') (b : Module.Basis (Fin 2) 𝒪' ρ.V)
    (η η' : Gℚ →* 𝒪'ˣ) (hη : ∀ σ : Gℚ, ρ.ρ σ (b 0) = ((η σ : 𝒪'ˣ) : 𝒪') • b 0)
    (hη' : ∀ σ : Gℚ, b.repr (ρ.ρ σ (b 1)) 1 = ((η' σ : 𝒪'ˣ) : 𝒪'))
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : W = K ∙ ((1 : K) ⊗ₜ[𝒪'] b 0))
    {σ : Gℚ} (h : η' σ = 1) : ∀ v : K ⊗[𝒪'] ρ.V, (ρ.ρ σ).baseChange K v - v ∈ W :=
  baseChange_apply_sub_mem_of_sub_mem_span (ρ.ρ σ) (b 0)
    (sub_mem_span_of_triangular b (ρ.ρ σ)
      (by rw [hη, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
            if_neg (by decide), smul_zero])
      (by rw [hη', h, Units.val_one]))
    W hW

end Wrappers
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

end W5bX
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

namespace Sol5bL

open GaloisRep GaloisRepAdic IsLocalRing
open scoped TensorProduct

abbrev Gal := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section Repr
variable {𝒪' : Type} [CommRing 𝒪'] {V : Type} [AddCommGroup V] [Module 𝒪' V]

lemma mem_ideal_smul_top_iff_repr (b : Module.Basis (Fin 2) 𝒪' V) (I : Ideal 𝒪') (v : V) :
    v ∈ I • (⊤ : Submodule 𝒪' V) ↔ ∀ i, b.repr v i ∈ I := by
  constructor
  · intro hv i
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro r hr w _
      simp only [LinearEquiv.map_smul, Finsupp.smul_apply]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      simp only [map_add, Finsupp.add_apply]
      exact I.add_mem hx hy
  · intro h
    have : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

end Repr
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

variable (p : ℕ) [Fact p.Prime]
variable (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable (ρ : GaloisRepAdic 𝒪')

section LevelActionDMA
variable (I : Ideal 𝒪')

lemma levelAction_one (m : ρ.V ⧸ (I • (⊤ : Submodule 𝒪' ρ.V))) :
    ρ.levelAction I 1 m = m := by
  induction m using Submodule.Quotient.induction_on with
  | _ v => simp [GaloisRepAdic.levelAction, Submodule.mapQ_apply]

lemma levelAction_mul (σ τ : Gal) (m : ρ.V ⧸ (I • (⊤ : Submodule 𝒪' ρ.V))) :
    ρ.levelAction I (σ * τ) m = ρ.levelAction I σ (ρ.levelAction I τ m) := by
  induction m using Submodule.Quotient.induction_on with
  | _ v => simp [GaloisRepAdic.levelAction, Submodule.mapQ_apply, map_mul]

noncomputable scoped instance instDMA_level : DistribMulAction Gal (ρ.V ⧸ (I • (⊤ : Submodule 𝒪' ρ.V))) where
  smul σ m := ρ.levelAction I σ m
  one_smul := levelAction_one 𝒪' ρ I
  mul_smul := levelAction_mul 𝒪' ρ I
  smul_zero _ := map_zero _
  smul_add _ := map_add _

lemma level_smul_def (σ : Gal) (m : ρ.V ⧸ (I • (⊤ : Submodule 𝒪' ρ.V))) :
    σ • m = ρ.levelAction I σ m := rfl

lemma level_smul_mk (σ : Gal) (v : ρ.V) :
    σ • (Submodule.Quotient.mk v : ρ.V ⧸ (I • (⊤ : Submodule 𝒪' ρ.V))) =
      Submodule.Quotient.mk (ρ.ρ σ v) := by
  change ρ.levelAction I σ _ = _
  rw [GaloisRepAdic.levelAction, Submodule.mapQ_apply]

end LevelActionDMA
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

section SubLine
variable (b : Module.Basis (Fin 2) 𝒪' ρ.V) (η : Gal →* 𝒪'ˣ)
variable (hη : ∀ σ : Gal, ρ.ρ σ (b 0) = (η σ : 𝒪') • b 0)

abbrev L₀ : Submodule 𝒪' ρ.V := Submodule.span 𝒪' {b 0}

lemma mem_L₀_iff (v : ρ.V) : v ∈ L₀ 𝒪' ρ b ↔ b.repr v 1 = 0 := by
  rw [L₀, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩; simp
  · intro h
    refine ⟨b.repr v 0, ?_⟩
    have := b.sum_repr v
    simp only [Fin.sum_univ_two, h, zero_smul, add_zero] at this
    exact this

section PerLevel
variable (k : ℕ)

abbrev Mk := ρ.V ⧸ ((maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' ρ.V))

def Nk : Type :=
  have := η
  (L₀ 𝒪' ρ b) ⧸ ((maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' (L₀ 𝒪' ρ b)))

noncomputable scoped instance : AddCommGroup (Nk 𝒪' ρ b η k) :=
  inferInstanceAs (AddCommGroup
    ((L₀ 𝒪' ρ b) ⧸ ((maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' (L₀ 𝒪' ρ b)))))

noncomputable scoped instance : Module 𝒪' (Nk 𝒪' ρ b η k) :=
  inferInstanceAs (Module 𝒪'
    ((L₀ 𝒪' ρ b) ⧸ ((maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' (L₀ 𝒪' ρ b)))))

noncomputable def Nk.mk (l : L₀ 𝒪' ρ b) : Nk 𝒪' ρ b η k := Submodule.Quotient.mk l

lemma Nk.mk_surjective : Function.Surjective (Nk.mk 𝒪' ρ b η k) :=
  Submodule.Quotient.mk_surjective _

lemma Nk.mk_smul (r : 𝒪') (l : L₀ 𝒪' ρ b) :
    Nk.mk 𝒪' ρ b η k (r • l) = r • Nk.mk 𝒪' ρ b η k l :=
  Submodule.Quotient.mk_smul _ r l

lemma Nk.mk_eq_zero (l : L₀ 𝒪' ρ b) :
    Nk.mk 𝒪' ρ b η k l = 0 ↔
      l ∈ ((maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' (L₀ 𝒪' ρ b))) :=
  Submodule.Quotient.mk_eq_zero _

noncomputable def n₀ : Nk 𝒪' ρ b η k :=
  Nk.mk 𝒪' ρ b η k ⟨b 0, Submodule.mem_span_singleton_self _⟩

noncomputable scoped instance instDMA_Nk : DistribMulAction Gal (Nk 𝒪' ρ b η k) where
  smul σ n := (η σ : 𝒪') • n
  one_smul n := by show ((η 1 : 𝒪'ˣ) : 𝒪') • n = n; simp
  mul_smul σ τ n := by
    show ((η (σ * τ) : 𝒪'ˣ) : 𝒪') • n = (η σ : 𝒪') • ((η τ : 𝒪') • n)
    rw [map_mul, Units.val_mul, mul_smul]
  smul_zero σ := by
    show ((η σ : 𝒪'ˣ) : 𝒪') • (0 : Nk 𝒪' ρ b η k) = 0; exact smul_zero _
  smul_add σ n₁ n₂ := by
    show ((η σ : 𝒪'ˣ) : 𝒪') • (n₁ + n₂) = (η σ : 𝒪') • n₁ + (η σ : 𝒪') • n₂
    exact smul_add _ _ _

@[scoped simp] lemma hact (σ : Gal) (n : Nk 𝒪' ρ b η k) : σ • n = (η σ : 𝒪') • n := rfl

lemma hgen (n : Nk 𝒪' ρ b η k) : ∃ x : 𝒪', n = x • n₀ 𝒪' ρ b η k := by
  obtain ⟨l, rfl⟩ := Nk.mk_surjective 𝒪' ρ b η k n
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp l.2
  exact ⟨x, by rw [n₀, ← Nk.mk_smul]; congr 1; exact Subtype.ext hx.symm⟩

lemma hann (x : 𝒪') :
    x • n₀ 𝒪' ρ b η k = 0 ↔ x ∈ (maximalIdeal 𝒪') ^ k := by
  rw [n₀, ← Nk.mk_smul, Nk.mk_eq_zero, Submodule.mem_smul_top_iff]
  show x • b 0 ∈ (maximalIdeal 𝒪') ^ k • L₀ 𝒪' ρ b ↔ _
  constructor
  · intro hmem
    have hle : (maximalIdeal 𝒪') ^ k • L₀ 𝒪' ρ b ≤
        (maximalIdeal 𝒪') ^ k • (⊤ : Submodule 𝒪' ρ.V) :=
      Submodule.smul_mono le_rfl le_top
    have := (mem_ideal_smul_top_iff_repr b _ _).mp (hle hmem) 0
    simpa using this
  · intro hx
    rw [show (x • b 0 : ρ.V) =
        ((x • ⟨b 0, Submodule.mem_span_singleton_self _⟩ : L₀ 𝒪' ρ b) : ρ.V) from rfl,
        ← Submodule.mem_smul_top_iff]
    exact Submodule.smul_mem_smul hx Submodule.mem_top

noncomputable def ιk : Nk 𝒪' ρ b η k →+ Mk 𝒪' ρ k :=
  (Submodule.mapQ _ _ (L₀ 𝒪' ρ b).subtype (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)).toAddMonoidHom

lemma ιk_mk (l : L₀ 𝒪' ρ b) :
    ιk 𝒪' ρ b η k (Nk.mk 𝒪' ρ b η k l) = Submodule.Quotient.mk (l : ρ.V) := rfl

include hη in

lemma ιk_equivariant (σ : Gal) (n : Nk 𝒪' ρ b η k) :
    ιk 𝒪' ρ b η k (σ • n) = σ • ιk 𝒪' ρ b η k n := by
  obtain ⟨x, rfl⟩ := hgen 𝒪' ρ b η k n
  rw [hact, smul_smul, n₀, ← Nk.mk_smul, ← Nk.mk_smul, ιk_mk, ιk_mk, level_smul_mk]
  congr 1
  show ((η σ : 𝒪') * x) • b 0 = ρ.ρ σ (x • b 0)
  rw [LinearMap.map_smul, hη, smul_smul, mul_comm]

lemma ιk_injective : Function.Injective (ιk 𝒪' ρ b η k) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  obtain ⟨x, rfl⟩ := hgen 𝒪' ρ b η k n
  rw [hann]
  rw [n₀, ← Nk.mk_smul, ιk_mk, Submodule.Quotient.mk_eq_zero] at hn
  have := (mem_ideal_smul_top_iff_repr b _ _).mp hn 0
  simpa using this

end PerLevel
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

section L0Finite
variable (hflat : ρ.IsFlatAt p)

omit [Fact (Nat.Prime p)] in
include hflat in

private lemma _root_.Sol5bL.finite_quotient_pow (k : ℕ) : Finite (𝒪' ⧸ (maximalIdeal 𝒪') ^ k) := by
  haveI : Finite (𝒪' ⧸ maximalIdeal 𝒪') := hflat.1
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

p2m_export "Sol5bL" "finite_quotient_pow"
end L0Finite
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

section L2Apply
variable (hflat : ρ.IsFlatAt p)

omit [Fact (Nat.Prime p)] in
include hflat hη in

theorem exists_subModel (k : ℕ) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (ratLocalizedAt p) H),
      Module.Finite (ratLocalizedAt p) H ∧ Module.Flat (ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ) ≃ Nk 𝒪' ρ b η k,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : Gal) (f g : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) := by

  haveI : Finite (𝒪' ⧸ (maximalIdeal 𝒪') ^ k) := finite_quotient_pow p 𝒪' ρ hflat k
  obtain ⟨G, _, _, hGfin, hGflat, hGcocomm, eG, heG_add, heG_act⟩ :=
    hflat.2 ((maximalIdeal 𝒪') ^ k) inferInstance

  have heG_act' : ∀ (σ : Gal) f g, (∀ x : G, g x = σ (f x)) → eG g = σ • (eG f) :=
    fun σ f g hfg => heG_act σ f g hfg

  exact GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p G eG heG_add heG_act'
    (ιk 𝒪' ρ b η k) (ιk_injective 𝒪' ρ b η k) (ιk_equivariant 𝒪' ρ b η hη k)

end L2Apply
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"
end SubLine
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT"

end Sol5bL
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

open scoped TensorProduct

namespace RibetIrr5b

open GaloisRepAdic

section Head

variable (p : ℕ) [Fact p.Prime]
variable (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable (ρ : GaloisRepAdic 𝒪')
variable (W : Submodule K (K ⊗[𝒪'] ρ.V))

noncomputable def lineLattice : Submodule 𝒪' ρ.V :=
  (W.restrictScalars 𝒪').comap (TensorProduct.mk 𝒪' K ρ.V 1)

theorem mem_lineLattice_of_smul_mem (c : 𝒪') (hc : c ≠ 0) (v : ρ.V)
    (h : c • v ∈ lineLattice 𝒪' K ρ W) : v ∈ lineLattice 𝒪' K ρ W := by
  have hinj : Function.Injective (algebraMap 𝒪' K) := IsFractionRing.injective 𝒪' K
  have hcK : algebraMap 𝒪' K c ≠ 0 := fun h0 => hc (hinj (by simpa using h0))
  have h1 : (1 : K) ⊗ₜ[𝒪'] (c • v) ∈ W := h
  have h2 : (1 : K) ⊗ₜ[𝒪'] (c • v) = algebraMap 𝒪' K c • ((1 : K) ⊗ₜ[𝒪'] v) := by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    simp [Algebra.smul_def, smul_eq_mul]
  have h3 : algebraMap 𝒪' K c • ((1 : K) ⊗ₜ[𝒪'] v) ∈ W := h2 ▸ h1
  have := W.smul_mem (algebraMap 𝒪' K c)⁻¹ h3
  rwa [inv_smul_smul₀ hcK] at this

omit [IsFractionRing 𝒪' K] in

theorem lineLattice_stable
    (hWstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V)
    (hv : v ∈ lineLattice 𝒪' K ρ W) : ρ.ρ σ v ∈ lineLattice 𝒪' K ρ W := by
  have h1 : (1 : K) ⊗ₜ[𝒪'] v ∈ W := hv
  have h2 := hWstab σ _ h1
  have h3 : (ρ.ρ σ).baseChange K ((1 : K) ⊗ₜ[𝒪'] v) = (1 : K) ⊗ₜ[𝒪'] (ρ.ρ σ v) :=
    LinearMap.baseChange_tmul _ _ _
  simp only [h3] at h2
  exact h2

end Head
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section Dichotomy

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']

open IsLocalRing

theorem iInf_maxIdeal_pow_eq_bot :
    ⨅ k : ℕ, maximalIdeal 𝒪' ^ k = ⊥ :=
  Ideal.iInf_pow_eq_bot_of_isLocalRing _ (Ideal.IsMaximal.ne_top inferInstance)

theorem eq_one_or_eq_one_of_levelwise (e e' d : 𝒪'ˣ)
    (hd : (e : 𝒪') * (e' : 𝒪') = (d : 𝒪')) (A : ℕ → ℕ)
    (hq : ∀ k : ℕ, 1 ≤ k →
      ((e : 𝒪') - (A k : ℕ)) * ((e : 𝒪') - 1) ∈ maximalIdeal 𝒪' ^ k)
    (hdet : ∀ k : ℕ, 1 ≤ k → (d : 𝒪') - (A k : ℕ) ∈ maximalIdeal 𝒪' ^ k) :
    e = 1 ∨ e' = 1 := by
  by_cases he : e = 1
  · exact Or.inl he
  right

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪'
  have hmax : maximalIdeal 𝒪' = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hx0 : (e : 𝒪') - 1 ≠ 0 := by
    intro h0
    exact he (Units.ext (by rw [Units.val_one, ← sub_eq_zero]; exact h0))
  obtain ⟨c, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ

  have key : ∀ m : ℕ, (e' : 𝒪') - 1 ∈ maximalIdeal 𝒪' ^ m := by
    intro m
    have h1 : 1 ≤ m + c + 1 := by omega
    have hqk := hq (m + c + 1) h1
    have hdk := hdet (m + c + 1) h1
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hqk hdk ⊢

    have hstep : π ^ (m + 1) ∣ (e : 𝒪') - (A (m + c + 1) : ℕ) := by
      rw [hxu] at hqk
      have h2 : π ^ (m + 1) * π ^ c ∣
          ((e : 𝒪') - (A (m + c + 1) : ℕ)) * (↑u * π ^ c) := by
        rw [← pow_add]
        have : m + 1 + c = m + c + 1 := by omega
        rw [this]
        exact hqk
      have h3 : π ^ (m + 1) ∣ ((e : 𝒪') - (A (m + c + 1) : ℕ)) * ↑u := by
        rcases h2 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        have hc0 : (π : 𝒪') ^ c ≠ 0 := pow_ne_zero _ hπ0
        apply mul_right_cancel₀ hc0
        calc ((e : 𝒪') - (A (m + c + 1) : ℕ)) * ↑u * π ^ c
            = ((e : 𝒪') - (A (m + c + 1) : ℕ)) * (↑u * π ^ c) := by ring
          _ = π ^ (m + 1) * π ^ c * s := hs
          _ = π ^ (m + 1) * s * π ^ c := by ring
      exact (Units.dvd_mul_right).mp h3

    have hdk' : π ^ (m + 1) ∣ (d : 𝒪') - (A (m + c + 1) : ℕ) := by
      refine dvd_trans ?_ hdk
      exact pow_dvd_pow _ (by omega)
    have hde : π ^ (m + 1) ∣ (d : 𝒪') - (e : 𝒪') := by
      have : (d : 𝒪') - (e : 𝒪') =
          ((d : 𝒪') - (A (m + c + 1) : ℕ)) - ((e : 𝒪') - (A (m + c + 1) : ℕ)) := by ring
      rw [this]
      exact dvd_sub hdk' hstep
    have hfac : (d : 𝒪') - (e : 𝒪') = (e : 𝒪') * ((e' : 𝒪') - 1) := by
      rw [← hd]; ring
    rw [hfac] at hde
    have : π ^ (m + 1) ∣ (e' : 𝒪') - 1 := (Units.dvd_mul_left).mp hde
    exact dvd_trans (pow_dvd_pow _ (by omega)) this

  have : (e' : 𝒪') - 1 ∈ ⨅ m : ℕ, maximalIdeal 𝒪' ^ m :=
    Submodule.mem_iInf _ |>.mpr key
  rw [iInf_maxIdeal_pow_eq_bot] at this
  have h0 : (e' : 𝒪') - 1 = 0 := by simpa using this
  exact Units.ext (by rw [Units.val_one, ← sub_eq_zero]; exact h0)

end Dichotomy
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section Globalize

variable {G : Type} [Group G]

theorem forall_eq_one_or_forall_eq_one {M M' : Type} [Monoid M] [Monoid M']
    (H : Subgroup G) (f : G →* M) (g : G →* M')
    (h : ∀ σ ∈ H, f σ = 1 ∨ g σ = 1) :
    (∀ σ ∈ H, f σ = 1) ∨ (∀ σ ∈ H, g σ = 1) := by
  by_cases hf : ∀ σ ∈ H, f σ = 1
  · exact Or.inl hf
  right
  simp only [not_forall] at hf
  obtain ⟨τ, hτH, hτ⟩ := hf
  intro σ hσH
  rcases h σ hσH with hfσ | hgσ
  · rcases h (σ * τ) (H.mul_mem hσH hτH) with hfστ | hgστ
    · exact absurd (by simpa [map_mul, hfσ] using hfστ) hτ
    · have hgτ : g τ = 1 := (h τ hτH).resolve_left hτ
      have hmul : g σ * g τ = 1 := by simpa [map_mul] using hgστ
      simpa [hgτ] using hmul
  · exact hgσ

open scoped Pointwise in

theorem forall_inertia_eq_one_of_base {M : Type} [CommMonoid M] {p : ℕ} (hp : p.Prime)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (P₀ : ValuationSubring (AlgebraicClosure ℚ)) (hP₀ : P₀.LiesOverPrime p)
    (h0 : ∀ σ ∈ P₀.inertiaSubgroupIn ℚ, f σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, f σ = 1 := by
  intro P hP σ hσ
  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp P₀ P hP₀ hP
  rw [← hg] at hσ
  have h1 : g⁻¹ * σ * g ∈ P₀.inertiaSubgroupIn ℚ :=
    ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul P₀ g hσ
  have h2 : f (g⁻¹ * σ * g) = 1 := h0 _ h1
  have h3 : f (g⁻¹ * σ * g) = f σ := by
    rw [map_mul, map_mul, mul_comm (f g⁻¹) (f σ), mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, mul_one]
  rwa [h3] at h2

end Globalize
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section CharPGlue

variable {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪']

theorem charP_residueField_of_mem_maximalIdeal (p : ℕ) (hp : p.Prime)
    (h : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪') :
    CharP (IsLocalRing.ResidueField 𝒪') p := by
  have h0 : (p : IsLocalRing.ResidueField 𝒪') = 0 := by
    have : (p : IsLocalRing.ResidueField 𝒪') =
        IsLocalRing.residue 𝒪' (p : 𝒪') := (map_natCast (IsLocalRing.residue 𝒪') p).symm
    rw [this]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h0

end CharPGlue
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

end RibetIrr5b
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

open scoped TensorProduct

namespace RibetIrr5b

section RankOne

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable {M : Type} [AddCommGroup M] [Module 𝒪' M]

theorem exists_generator_of_finrank_one [Module.Free 𝒪' M] [Module.Finite 𝒪' M]
    (h1 : Module.finrank 𝒪' M = 1) :
    ∃ u : M, (∀ x : M, ∃ c : 𝒪', x = c • u) ∧ ∀ c : 𝒪', c • u = 0 → c = 0 := by
  classical
  have hb := Module.Free.chooseBasis 𝒪' M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex 𝒪' M) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact h1
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hcard
  refine ⟨hb i0, fun x => ?_, fun c hc => ?_⟩
  · refine ⟨hb.repr x i0, ?_⟩
    conv_lhs => rw [← hb.sum_repr x]
    rw [Finset.sum_eq_single i0]
    · intro j _ hj
      exact absurd (hi0 j) hj
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · have := congrArg (fun z => hb.repr z i0) hc
    simpa [hb.repr_self] using this

end RankOne
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section Chars

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
variable {V : Type} [AddCommGroup V] [Module 𝒪' V]

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] in

theorem exists_adapted_basis (L : Submodule 𝒪' V)
    (u : V) (hu : u ∈ L) (hLgen : ∀ x ∈ L, ∃ c : 𝒪', x = c • u)
    (hu0 : ∀ c : 𝒪', c • u = 0 → c = 0)
    (w : V) (hsp : ∀ z : V, ∃ c : 𝒪', z + c • w ∈ L)
    (hli : ∀ c : 𝒪', c • w ∈ L → c = 0) :
    ∃ b : Module.Basis (Fin 2) 𝒪' V, b 0 = u ∧ b 1 = w := by
  classical
  have hind : LinearIndependent 𝒪' ![u, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg

    have hw1 : g 1 • w ∈ L := by
      have heq : g 1 • w = -(g 0 • u) := by
        have := eq_neg_of_add_eq_zero_right hg
        exact this
      rw [heq]
      exact L.neg_mem (L.smul_mem _ hu)
    have hg1 : g 1 = 0 := hli _ hw1
    have hg0 : g 0 = 0 := by
      apply hu0
      have : g 0 • u + g 1 • w = 0 := hg
      rwa [hg1, zero_smul, add_zero] at this
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  have hspan : ⊤ ≤ Submodule.span 𝒪' (Set.range ![u, w]) := by
    intro z _
    obtain ⟨c, hc⟩ := hsp z
    obtain ⟨c', hc'⟩ := hLgen _ hc
    have hz : z = c' • u + -c • w := by
      have h1 : z = c' • u - c • w := eq_sub_of_add_eq hc'
      rw [h1, sub_eq_add_neg, ← neg_smul]
    rw [hz]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  refine ⟨Module.Basis.mk hind hspan, ?_, ?_⟩ <;> simp [Module.Basis.coe_mk]

omit [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] in

theorem repr_apply_one_eq_zero_of_stable (L : Submodule 𝒪' V)
    (b : Module.Basis (Fin 2) 𝒪' V) (hb0 : b 0 ∈ L)
    (hLgen : ∀ x ∈ L, ∃ c : 𝒪', x = c • b 0)
    (f : Module.End 𝒪' V) (hf : ∀ x ∈ L, f x ∈ L) :
    b.repr (f (b 0)) 1 = 0 := by
  obtain ⟨c, hc⟩ := hLgen _ (hf _ hb0)
  rw [hc]
  simp [Module.Basis.repr_self]

end Chars
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section Eta

variable {𝒪' : Type} [CommRing 𝒪']
variable {V : Type} [AddCommGroup V] [Module 𝒪' V]
variable {G : Type} [Group G]

noncomputable def etaFun (ρ : G →* Module.End 𝒪' V) (b : Module.Basis (Fin 2) 𝒪' V)
    (σ : G) : 𝒪' :=
  b.repr (ρ σ (b 0)) 0

noncomputable def etaFun' (ρ : G →* Module.End 𝒪' V) (b : Module.Basis (Fin 2) 𝒪' V)
    (σ : G) : 𝒪' :=
  b.repr (ρ σ (b 1)) 1

variable (ρ : G →* Module.End 𝒪' V) (b : Module.Basis (Fin 2) 𝒪' V)

theorem rho_apply_b0 (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ : G) :
    ρ σ (b 0) = etaFun ρ b σ • b 0 := by
  obtain ⟨c, hc⟩ := hstab σ
  have hcoord : etaFun ρ b σ = c := by
    unfold etaFun
    rw [hc]
    simp [Module.Basis.repr_self]
  rw [hcoord, hc]

theorem etaFun_one : etaFun ρ b 1 = 1 := by
  unfold etaFun
  simp [Module.Basis.repr_self]

theorem etaFun_mul (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ τ : G) :
    etaFun ρ b (σ * τ) = etaFun ρ b σ * etaFun ρ b τ := by
  have h1 : ρ (σ * τ) (b 0) = (etaFun ρ b τ * etaFun ρ b σ) • b 0 := by
    rw [map_mul]
    have h2 : (ρ σ * ρ τ) (b 0) = ρ σ (ρ τ (b 0)) := rfl
    rw [h2, rho_apply_b0 ρ b hstab τ, map_smul, rho_apply_b0 ρ b hstab σ, smul_smul]
  unfold etaFun
  rw [h1]
  simp [Module.Basis.repr_self, etaFun, mul_comm]

noncomputable def eta (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) : G →* 𝒪'ˣ where
  toFun σ :=
    { val := etaFun ρ b σ
      inv := etaFun ρ b σ⁻¹
      val_inv := by rw [← etaFun_mul ρ b hstab, mul_inv_cancel, etaFun_one]
      inv_val := by rw [← etaFun_mul ρ b hstab, inv_mul_cancel, etaFun_one] }
  map_one' := by ext; simp [etaFun_one ρ b]
  map_mul' σ τ := by ext; simp [etaFun_mul ρ b hstab]

@[scoped simp] theorem eta_coe (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ : G) :
    ((eta ρ b hstab σ : 𝒪'ˣ) : 𝒪') = etaFun ρ b σ := rfl

theorem rho_apply_b1 (σ : G) :
    ρ σ (b 1) = b.repr (ρ σ (b 1)) 0 • b 0 + etaFun' ρ b σ • b 1 := by
  conv_lhs => rw [← b.sum_repr (ρ σ (b 1))]
  rw [Fin.sum_univ_two]
  rfl

theorem etaFun'_one : etaFun' ρ b 1 = 1 := by
  unfold etaFun'
  simp [Module.Basis.repr_self]

theorem etaFun'_mul (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ τ : G) :
    etaFun' ρ b (σ * τ) = etaFun' ρ b σ * etaFun' ρ b τ := by
  have h1 : ρ (σ * τ) (b 1) = ρ σ (ρ τ (b 1)) := by rw [map_mul]; rfl
  unfold etaFun'
  rw [h1]
  conv_lhs => rw [rho_apply_b1 ρ b τ]
  rw [map_add, map_smul, map_smul, rho_apply_b0 ρ b hstab σ]
  conv_lhs => rw [rho_apply_b1 ρ b σ]
  simp [Module.Basis.repr_self, etaFun', smul_smul, mul_comm]

noncomputable def eta' (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) : G →* 𝒪'ˣ where
  toFun σ :=
    { val := etaFun' ρ b σ
      inv := etaFun' ρ b σ⁻¹
      val_inv := by rw [← etaFun'_mul ρ b hstab, mul_inv_cancel, etaFun'_one]
      inv_val := by rw [← etaFun'_mul ρ b hstab, inv_mul_cancel, etaFun'_one] }
  map_one' := by ext; simp [etaFun'_one ρ b]
  map_mul' σ τ := by ext; simp [etaFun'_mul ρ b hstab]

@[scoped simp] theorem eta'_coe (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ : G) :
    ((eta' ρ b hstab σ : 𝒪'ˣ) : 𝒪') = etaFun' ρ b σ := rfl

theorem det_eq_eta_mul_eta' (hstab : ∀ σ : G, ∃ c : 𝒪', ρ σ (b 0) = c • b 0) (σ : G) :
    LinearMap.det (ρ σ) = etaFun ρ b σ * etaFun' ρ b σ := by
  rw [← LinearMap.det_toMatrix b]
  rw [Matrix.det_fin_two]
  have h00 : LinearMap.toMatrix b b (ρ σ) 0 0 = etaFun ρ b σ := by
    rw [LinearMap.toMatrix_apply]
    rfl
  have h11 : LinearMap.toMatrix b b (ρ σ) 1 1 = etaFun' ρ b σ := by
    rw [LinearMap.toMatrix_apply]
    rfl
  have h10 : LinearMap.toMatrix b b (ρ σ) 1 0 = 0 := by
    rw [LinearMap.toMatrix_apply]
    rw [rho_apply_b0 ρ b hstab σ]
    simp [Module.Basis.repr_self]
  rw [h00, h11, h10]
  ring

end Eta
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

section ADatum

theorem exists_pow_datum (p : ℕ) [Fact p.Prime] (k : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 → σ μ = μ ^ a := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  refine ⟨((modularCyclotomicCharacter' (AlgebraicClosure ℚ) (p ^ k)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :
        ZMod (Nat.card { x // x ∈ rootsOfUnity (p ^ k) (AlgebraicClosure ℚ) }))).val, ?_⟩
  intro μ hμ
  by_cases hμ0 : μ = 0
  · rw [hμ0] at hμ
    exact absurd hμ (by simp [zero_pow (NeZero.ne (p ^ k))])
  · have htmem : Units.mk0 μ hμ0 ∈ rootsOfUnity (p ^ k) (AlgebraicClosure ℚ) := by
      rw [mem_rootsOfUnity]
      ext
      simpa using hμ
    have hspec := modularCyclotomicCharacter'.spec' (AlgebraicClosure ℚ) (p ^ k)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) htmem
    simpa using hspec

end ADatum
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL"

end RibetIrr5b
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

open scoped TensorProduct

namespace RibetIrr5b

section Rank

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪']
variable {K : Type} [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable {V : Type} [AddCommGroup V] [Module 𝒪' V]

omit [IsDomain 𝒪'] [IsFractionRing 𝒪' K] in

theorem baseChange_repr_one_tmul (b : Module.Basis (Fin 2) 𝒪' V) (v : V) (i : Fin 2) :
    (b.baseChange K).repr ((1 : K) ⊗ₜ[𝒪'] v) i = algebraMap 𝒪' K (b.repr v i) := by
  rw [Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]

omit [IsDomain 𝒪'] in

theorem one_tmul_injective (b : Module.Basis (Fin 2) 𝒪' V) :
    Function.Injective (fun v : V => ((1 : K) ⊗ₜ[𝒪'] v : K ⊗[𝒪'] V)) := by
  intro v w h
  apply b.repr.injective
  ext i
  apply IsFractionRing.injective 𝒪' K
  rw [← baseChange_repr_one_tmul (K := K) b v i, ← baseChange_repr_one_tmul (K := K) b w i]
  exact congrArg (fun x : K ⊗[𝒪'] V => (b.baseChange K).repr x i) h

omit [IsDomain 𝒪'] in

theorem linearIndependent_one_tmul (b : Module.Basis (Fin 2) 𝒪' V)
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent 𝒪' v) :
    LinearIndependent K (fun i => ((1 : K) ⊗ₜ[𝒪'] (v i) : K ⊗[𝒪'] V)) := by
  have h1 : LinearIndependent 𝒪' (fun i => ((1 : K) ⊗ₜ[𝒪'] (v i) : K ⊗[𝒪'] V)) :=
    hv.map' (TensorProduct.mk 𝒪' K V 1) (LinearMap.ker_eq_bot.mpr (one_tmul_injective b))
  exact (LinearIndependent.iff_fractionRing 𝒪' K).mp h1

omit [IsDomain 𝒪'] [IsFractionRing 𝒪' K] in

theorem algebraMap_smul_one_tmul (c : 𝒪') (v : V) :
    algebraMap 𝒪' K c • ((1 : K) ⊗ₜ[𝒪'] v) = (1 : K) ⊗ₜ[𝒪'] (c • v) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem exists_smul_eq_one_tmul (x : K ⊗[𝒪'] V) :
    ∃ (c : 𝒪') (v : V), c ≠ 0 ∧ algebraMap 𝒪' K c • x = (1 : K) ⊗ₜ[𝒪'] v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by rw [smul_zero, TensorProduct.tmul_zero]⟩
  | tmul k v =>
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors 𝒪') k
    obtain ⟨n, hn⟩ := hint
    have hk : algebraMap 𝒪' K d * k = algebraMap 𝒪' K n := by
      rw [hn, Algebra.smul_def]
    refine ⟨d, n • v, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, hk, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c, v, hc, hcx⟩ := hx
    obtain ⟨c', v', hc', hcy⟩ := hy
    refine ⟨c * c', c' • v + c • v', mul_ne_zero hc hc', ?_⟩
    have e1 : (algebraMap 𝒪' K c * algebraMap 𝒪' K c') • x = (1 : K) ⊗ₜ[𝒪'] (c' • v) := by
      rw [mul_comm, mul_smul, hcx, algebraMap_smul_one_tmul]
    have e2 : (algebraMap 𝒪' K c * algebraMap 𝒪' K c') • y = (1 : K) ⊗ₜ[𝒪'] (c • v') := by
      rw [mul_smul, hcy, algebraMap_smul_one_tmul]
    rw [smul_add, map_mul, e1, e2, TensorProduct.tmul_add]

end Rank
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

end RibetIrr5b
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

open scoped TensorProduct

namespace RibetIrr5b

section LatticePackageS6

variable {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪']
variable {K : Type} [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
variable {V : Type} [AddCommGroup V] [Module 𝒪' V]

omit [IsDomain 𝒪'] [IsFractionRing 𝒪' K] in

theorem s6_algebraMap_smul_one_tmul (c : 𝒪') (v : V) :
    algebraMap 𝒪' K c • ((1 : K) ⊗ₜ[𝒪'] v) = (1 : K) ⊗ₜ[𝒪'] (c • v) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem s6_exists_smul_eq_one_tmul (x : K ⊗[𝒪'] V) :
    ∃ (c : 𝒪') (v : V), c ≠ 0 ∧ algebraMap 𝒪' K c • x = (1 : K) ⊗ₜ[𝒪'] v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by rw [smul_zero, TensorProduct.tmul_zero]⟩
  | tmul k v =>
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors 𝒪') k
    obtain ⟨n, hn⟩ := hint
    have hk : algebraMap 𝒪' K d * k = algebraMap 𝒪' K n := by
      rw [hn, Algebra.smul_def]
    refine ⟨d, n • v, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, hk, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c, v, hc, hcx⟩ := hx
    obtain ⟨c', v', hc', hcy⟩ := hy
    refine ⟨c * c', c' • v + c • v', mul_ne_zero hc hc', ?_⟩
    have e1 : (algebraMap 𝒪' K c * algebraMap 𝒪' K c') • x = (1 : K) ⊗ₜ[𝒪'] (c' • v) := by
      rw [mul_comm, mul_smul, hcx, s6_algebraMap_smul_one_tmul]
    have e2 : (algebraMap 𝒪' K c * algebraMap 𝒪' K c') • y = (1 : K) ⊗ₜ[𝒪'] (c • v') := by
      rw [mul_smul, hcy, s6_algebraMap_smul_one_tmul]
    rw [smul_add, map_mul, e1, e2, TensorProduct.tmul_add]

end LatticePackageS6
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

section LatticePackage

open GaloisRepAdic

theorem lattice_package (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ : GaloisRepAdic 𝒪') (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : Module.finrank K W = 1)
    (hWstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W) :
    ∃ b : Module.Basis (Fin 2) 𝒪' ρ.V,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ c : 𝒪', ρ.ρ σ (b 0) = c • b 0) ∧
      W = K ∙ ((1 : K) ⊗ₜ[𝒪'] b 0) := by
  classical
  haveI := ρ.instFree
  haveI := ρ.instFinite
  have hinj : Function.Injective (algebraMap 𝒪' K) := IsFractionRing.injective 𝒪' K
  have hne0 : ∀ c : 𝒪', c ≠ 0 → algebraMap 𝒪' K c ≠ 0 := fun c hc h0 =>
    hc (hinj (by rw [h0, map_zero]))

  set L : Submodule 𝒪' ρ.V := lineLattice 𝒪' K ρ W with hLdef
  have hmemL : ∀ v : ρ.V, v ∈ L ↔ (1 : K) ⊗ₜ[𝒪'] v ∈ W := fun v => Iff.rfl
  have hsat : ∀ (r : 𝒪') (v : ρ.V), r ≠ 0 → r • v ∈ L → v ∈ L :=
    fun r v hr h => mem_lineLattice_of_smul_mem 𝒪' K ρ W r hr v h

  have hWne : W ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot K (K ⊗[𝒪'] ρ.V)] at hW
    exact zero_ne_one hW
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨c0, v0, hc0, hcv0⟩ := s6_exists_smul_eq_one_tmul (K := K) w
  have hv0L : v0 ∈ L := by
    rw [hmemL, ← hcv0]
    exact W.smul_mem _ hwW
  have hv00 : v0 ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, smul_eq_zero] at hcv0
    exact hcv0.elim (hne0 c0 hc0) hw0

  obtain ⟨n, bM, bN, f, a, hsnf⟩ :=
    Submodule.smithNormalForm (Module.finBasisOfFinrankEq 𝒪' ρ.V ρ.finrank_eq) L
  have ha : ∀ i, a i ≠ 0 := by
    intro i hai
    have h1 : (bN i : ρ.V) = 0 := by rw [hsnf i, hai, zero_smul]
    exact bN.ne_zero i (Subtype.ext h1)
  have hfL : ∀ i, bM (f i) ∈ L := fun i =>
    hsat (a i) _ (ha i) (by rw [← hsnf i]; exact (bN i).2)

  have hn2 : n ≤ 2 := by simpa using Fintype.card_le_of_embedding f
  have hn0 : n ≠ 0 := by
    intro hn0
    subst hn0
    apply hv00
    have h := bN.ext_elem (x := (⟨v0, hv0L⟩ : L)) (y := 0) (fun i => Fin.elim0 i)
    exact congrArg Subtype.val h
  have hlt2 : n < 2 := by
    by_contra hge
    rw [not_lt] at hge
    have hlt0 : 0 < n := by omega
    have hlt1 : 1 < n := by omega
    have h12 : f ⟨0, hlt0⟩ ≠ f ⟨1, hlt1⟩ := fun h =>
      absurd (congrArg Fin.val (f.injective h)) (by simp)
    have hall : ∀ j : Fin 2, bM j ∈ L := by
      intro j
      by_cases hj : j = f ⟨0, hlt0⟩
      · rw [hj]
        exact hfL _
      · have hj' : j = f ⟨1, hlt1⟩ := by
          apply Fin.ext
          have h1 : j.val ≠ (f ⟨0, hlt0⟩).val := fun h => hj (Fin.ext h)
          have h2 : (f ⟨0, hlt0⟩).val ≠ (f ⟨1, hlt1⟩).val := fun h => h12 (Fin.ext h)
          have hjl := j.2
          have hl0 := (f ⟨0, hlt0⟩).2
          have hl1 := (f ⟨1, hlt1⟩).2
          omega
        rw [hj']
        exact hfL _
    have hLtop : L = ⊤ := by
      rw [eq_top_iff, ← bM.span_eq]
      exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)
    have hWtop : W = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => exact W.zero_mem
      | tmul k v =>
        have hv : (1 : K) ⊗ₜ[𝒪'] v ∈ W := by
          rw [← hmemL, hLtop]
          exact Submodule.mem_top
        have hkv : k ⊗ₜ[𝒪'] v = k • ((1 : K) ⊗ₜ[𝒪'] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hkv]
        exact W.smul_mem k hv
      | add x y hx hy => exact W.add_mem hx hy
    rw [hWtop, finrank_top, Module.finrank_baseChange, ρ.finrank_eq] at hW
    exact absurd hW (by decide)
  obtain rfl : n = 1 := by omega

  have hu : bM (f 0) ∈ L := hfL 0
  have hLgen : ∀ x ∈ L, ∃ r : 𝒪', x = r • bM (f 0) := by
    intro x hx
    refine ⟨bN.repr ⟨x, hx⟩ 0 * a 0, ?_⟩
    have h1 : (⟨x, hx⟩ : L) = bN.repr ⟨x, hx⟩ 0 • bN 0 := by
      have h := bN.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_one] at h
      exact h.symm
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_smul, hsnf 0, smul_smul] at h2
    exact h2
  have hb0 : (bM.reindex (Equiv.swap (f 0) 0)) 0 = bM (f 0) := by
    rw [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  refine ⟨bM.reindex (Equiv.swap (f 0) 0), fun σ => ?_, ?_⟩
  · rw [hb0]
    exact hLgen _ (lineLattice_stable 𝒪' K ρ W hWstab σ _ hu)
  · rw [hb0]
    apply le_antisymm
    · intro x hx
      obtain ⟨c1, v1, hc1, hcv1⟩ := s6_exists_smul_eq_one_tmul (K := K) x
      have hv1L : v1 ∈ L := by
        rw [hmemL, ← hcv1]
        exact W.smul_mem _ hx
      obtain ⟨r, hr⟩ := hLgen v1 hv1L
      refine Submodule.mem_span_singleton.mpr ⟨(algebraMap 𝒪' K c1)⁻¹ * algebraMap 𝒪' K r, ?_⟩
      rw [mul_smul, s6_algebraMap_smul_one_tmul, ← hr, ← hcv1, inv_smul_smul₀ (hne0 c1 hc1)]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (hmemL _).mp hu

end LatticePackage
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

end RibetIrr5b
p2m_reactivate "P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.W5bT P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.Sol5bL P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.RibetIrr5b"

theorem solution (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ : GaloisRepAdic 𝒪') (hflat : ρ.IsFlatAt p) (hdet : ρ.DetIsCyclotomic p)
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : Module.finrank K W = 1)
    (hWstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W) :
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρ.ρ σ).baseChange K w = w) ∨
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : K ⊗[𝒪'] ρ.V, (ρ.ρ σ).baseChange K v - v ∈ W) := by
  classical

  by_cases hex : ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p
  case neg =>
    left
    intro P hP
    exact absurd ⟨P, hP⟩ hex
  obtain ⟨P₀, hP₀⟩ := hex

  obtain ⟨b, hstab, hWeq⟩ := RibetIrr5b.lattice_package 𝒪' K ρ W hW hWstab
  set η : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* 𝒪'ˣ :=
    RibetIrr5b.eta ρ.ρ b hstab with hηdef
  set η' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* 𝒪'ˣ :=
    RibetIrr5b.eta' ρ.ρ b hstab with hη'def
  have hη : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρ.ρ σ (b 0) = ((η σ : 𝒪'ˣ) : 𝒪') • b 0 := fun σ => by
    rw [hηdef, RibetIrr5b.eta_coe]
    exact RibetIrr5b.rho_apply_b0 ρ.ρ b hstab σ
  have hη' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      b.repr (ρ.ρ σ (b 1)) 1 = ((η' σ : 𝒪'ˣ) : 𝒪') := fun σ => by
    rw [hη'def, RibetIrr5b.eta'_coe]
    rfl

  have hp𝔪 : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' := hdet.1
  haveI : CharP (IsLocalRing.ResidueField 𝒪') p :=
    RibetIrr5b.charP_residueField_of_mem_maximalIdeal p Fact.out hp𝔪

  have hdich : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, η σ = 1 ∨ η' σ = 1 := by
    intro P hP σ hσ
    choose A hA using fun k => RibetIrr5b.exists_pow_datum p k σ
    apply RibetIrr5b.eq_one_or_eq_one_of_levelwise (η σ) (η' σ) (η σ * η' σ)
      (Units.val_mul _ _).symm A
    ·
      intro k _
      obtain ⟨H, _, _, hHfin, hHflat, hHcocomm, e', he'_add, he'_act⟩ :=
        Sol5bL.exists_subModel p 𝒪' ρ b η hη hflat k
      exact W5bT.level_quadratic_of_basis p ρ b η hη hp𝔪 P hP k
        (Sol5bL.Nk 𝒪' ρ b η k) (Sol5bL.n₀ 𝒪' ρ b η k)
        (Sol5bL.hgen 𝒪' ρ b η k) (Sol5bL.hann 𝒪' ρ b η k) (Sol5bL.hact 𝒪' ρ b η k)
        H e' he'_add he'_act hσ (A k) (hA k)
    ·
      intro k _
      have hd := hdet.2 k σ (A k) (hA k)
      have hdet_eta : LinearMap.det (ρ.ρ σ) = ((η σ * η' σ : 𝒪'ˣ) : 𝒪') := by
        rw [Units.val_mul, hηdef, hη'def, RibetIrr5b.eta_coe, RibetIrr5b.eta'_coe]
        exact RibetIrr5b.det_eq_eta_mul_eta' ρ.ρ b hstab σ
      rw [hdet_eta] at hd
      rw [Ideal.mem_span_singleton] at hd
      obtain ⟨t, ht⟩ := hd
      rw [ht]
      have hpk : ((p ^ k : ℕ) : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' ^ k := by
        have hcast : ((p ^ k : ℕ) : 𝒪') = ((p : 𝒪')) ^ k := by push_cast; ring
        rw [hcast]
        exact Ideal.pow_mem_pow hp𝔪 k
      exact Ideal.mul_mem_right t _ hpk

  rcases RibetIrr5b.forall_eq_one_or_forall_eq_one (P₀.inertiaSubgroupIn ℚ) η η'
      (hdich P₀ hP₀) with h0 | h0
  · left
    have hall := RibetIrr5b.forall_inertia_eq_one_of_base Fact.out η P₀ hP₀ h0
    intro P hP σ hσ w hw
    exact W5bX.disjunct_one ρ b η hη W hWeq (hall P hP σ hσ) w hw
  · right
    have hall := RibetIrr5b.forall_inertia_eq_one_of_base Fact.out η' P₀ hP₀ h0
    intro P hP σ hσ v
    exact W5bX.disjunct_two ρ b η η' hη hη' W hWeq (hall P hP σ hσ) v

end S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
end P2MW
export P2MW.S_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt (solution)
