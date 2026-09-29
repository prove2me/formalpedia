-- Prove2me | solution 1 for Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/28a3da7d-80d4-5ce0-8e49-e73e9bfe6bf5

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

open scoped Pointwise

noncomputable section

namespace P2C0DivDensity

p2m_open "NumberField Ideal NumberField.Ideal ValuationSubring"

section Place

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem smul_sub_pow_mem_nonunits
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ} (h : A.IsFrobeniusAt σ q)
    {x : L} (hx : x ∈ A) : σ x - x ^ q ∈ A.nonunits := by
  set a : A := ⟨x, hx⟩ with ha
  set g : A.decompositionSubgroup K := ⟨σ, h.mem_decompositionSubgroup⟩ with hg
  have h1 : IsLocalRing.residue A (g • a) = IsLocalRing.residue A (a ^ q) := by
    rw [map_pow, IsLocalRing.ResidueField.residue_smul]
    exact h.smul_residue_eq _
  have h2 : g • a - a ^ q ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a ^ q) = 0 := by
      rw [map_sub, h1, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a ^ q : A) : L) = σ x - x ^ q := rfl
  have := (coe_mem_nonunits_iff (A := A)).mpr h2
  rwa [hcoe] at this

theorem exists_liesOverPrime (L : Type*) [Field L] [CharZero L] {q : ℕ} (hq : q.Prime) :
    ∃ A : ValuationSubring L, A.LiesOverPrime q := by
  set R : Subring L := ⊥ with hR
  have hqR : ¬ IsUnit ((q : ℕ) : R) := by
    intro hu
    obtain ⟨u, hu⟩ := hu

    have hsurj : ∀ r : R, ∃ n : ℤ, (n : R) = r := by
      rintro ⟨r, hr⟩
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hr
      exact ⟨n, Subtype.ext (by simp)⟩
    obtain ⟨a, ha⟩ := hsurj u
    obtain ⟨b, hb⟩ := hsurj ↑u⁻¹
    have hab : (a : R) * b = 1 := by rw [ha, hb, Units.mul_inv]
    have hab' : (a : L) * b = 1 := by
      have := congrArg (Subtype.val) hab
      simpa using this
    have haq : (a : L) = q := by
      have := congrArg (Subtype.val) (ha.trans hu)
      simpa using this
    have hint : (a * b : ℤ) = 1 := by exact_mod_cast hab'
    have ha1 : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hint
    have hq2 := hq.two_le
    rcases ha1 with rfl | rfl
    · have : (q : L) = 1 := by simpa using haq.symm
      have : q = 1 := by exact_mod_cast this
      omega
    · have h1 : ((q : ℤ) : L) = ((-1 : ℤ) : L) := by push_cast; simpa using haq.symm
      have : (q : ℤ) = -1 := Int.cast_injective h1
      omega
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (Ideal.span {((q : ℕ) : R)})
    (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  exact ⟨B, hB ⟨_, Ideal.subset_span rfl, by simp⟩⟩

end Place

section PlaceIdeal

variable {L : Type*} [Field L]
variable (A : ValuationSubring L) (F : Type*) [Field F] [Algebra F L]

theorem algebraMap_ringOfIntegers_mem (x : 𝓞 F) :
    algebraMap F L (algebraMap (𝓞 F) F x) ∈ A := by
  have hint : IsIntegral ℤ (algebraMap F L (algebraMap (𝓞 F) F x)) :=
    (RingOfIntegers.isIntegral_coe x).map ((algebraMap F L).toIntAlgHom)
  haveI : IsScalarTower ℤ A L := IsScalarTower.of_algebraMap_eq fun n => by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  have hintA : IsIntegral A (algebraMap F L (algebraMap (𝓞 F) F x)) := hint.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  exact ha ▸ a.2

def placeIdealHom : 𝓞 F →+* A :=
  ((algebraMap F L).comp (algebraMap (𝓞 F) F)).codRestrict A.toSubring
    (algebraMap_ringOfIntegers_mem A F)

@[scoped simp]
theorem coe_placeIdealHom_apply (x : 𝓞 F) :
    (placeIdealHom A F x : L) = algebraMap F L (algebraMap (𝓞 F) F x) :=
  rfl

def placeIdeal : Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal A).comap (placeIdealHom A F)

theorem mem_placeIdeal_iff {x : 𝓞 F} :
    x ∈ placeIdeal A F ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits := by
  unfold placeIdeal
  rw [Ideal.mem_comap, ← coe_mem_nonunits_iff, coe_placeIdealHom_apply]

scoped instance : (placeIdeal A F).IsPrime := by
  unfold placeIdeal
  haveI : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  exact Ideal.IsPrime.comap _

variable {q : ℕ}

theorem natCast_mem_placeIdeal (hA : A.LiesOverPrime q) : (q : 𝓞 F) ∈ placeIdeal A F := by
  rw [mem_placeIdeal_iff, map_natCast, map_natCast]
  exact hA

theorem placeIdeal_ne_bot [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    placeIdeal A F ≠ ⊥ := by
  intro hbot
  have hq0 : (q : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  exact hq0 (by simpa [hbot] using natCast_mem_placeIdeal A F hA)

theorem placeIdeal_under_eq [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    (placeIdeal A F).under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq)).irreducible
  have h1 : Ideal.span {(q : ℤ)} ≤ (placeIdeal A F).under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap,
      map_natCast]
    exact natCast_mem_placeIdeal A F hA
  have h2 : ((placeIdeal A F).under ℤ).IsPrime := by
    rw [Ideal.under]; exact Ideal.IsPrime.comap _
  exact (hmax.eq_of_le h2.ne_top h1).symm

theorem card_quotient_under_placeIdeal [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    Nat.card (ℤ ⧸ (placeIdeal A F).under ℤ) = q := by
  rw [placeIdeal_under_eq A F hq hA, Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv,
    Nat.card_zmod]

end PlaceIdeal

section Restriction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F : Type*) [Field F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L] [Normal ℚ F]
variable (A : ValuationSubring L)

theorem isArithFrobAt_restrictNormalHom_of_isFrobeniusAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) (placeIdeal A F) := by
  intro x
  rw [card_quotient_under_placeIdeal A F hℓ hA, mem_placeIdeal_iff]
  have hsmul : algebraMap (𝓞 F) F
      (MulSemiringAction.toAlgHom ℤ (𝓞 F) (AlgEquiv.restrictNormalHom F τ) x) =
      AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x) := rfl
  have hrestrict : algebraMap F L (AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)) =
      τ (algebraMap F L (algebraMap (𝓞 F) F x)) := by
    have h : AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)
        = τ.restrictNormal F (algebraMap (𝓞 F) F x) := rfl
    rw [h, AlgEquiv.restrictNormal_commutes]
  rw [map_sub, map_pow, map_sub, map_pow, hsmul, hrestrict]
  exact smul_sub_pow_mem_nonunits hτ (algebraMap_ringOfIntegers_mem A F x)

end Restriction

section Ramified

variable (F : Type*) [Field F] [NumberField F]

theorem exists_smul_ne_of_ne_one {ι : F ≃ₐ[ℚ] F} (hι : ι ≠ 1) :
    ∃ x : 𝓞 F, ι • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 F, ι • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hι (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (K := F) z
  have hx : ι (algebraMap (𝓞 F) F x) = algebraMap (𝓞 F) F x := congrArg (algebraMap (𝓞 F) F)
    (hcon x)
  have hy' : ι (algebraMap (𝓞 F) F y) = algebraMap (𝓞 F) F y := congrArg (algebraMap (𝓞 F) F)
    (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_isPrime_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    {Q : Ideal (𝓞 F) | Q.IsPrime ∧ I ≤ Q}.Finite := by
  haveI : Finite ((𝓞 F) ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Finite (Ideal ((𝓞 F) ⧸ I)) :=
    Finite.of_injective (fun J : Ideal ((𝓞 F) ⧸ I) => (J : Set ((𝓞 F) ⧸ I)))
      fun _ _ h => SetLike.coe_injective h
  refine Set.Finite.of_finite_image (f := fun Q => Q.map (Ideal.Quotient.mk I))
    (Set.toFinite _) ?_
  rintro Q₁ ⟨-, hIQ₁⟩ Q₂ ⟨-, hIQ₂⟩ heq
  have key : ∀ Q : Ideal (𝓞 F), I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hIQ
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIQ]
  rw [← key Q₁ hIQ₁, ← key Q₂ hIQ₂]
  exact congrArg _ heq

def displacementIdeal (ι : F ≃ₐ[ℚ] F) : Ideal (𝓞 F) :=
  Ideal.span (Set.range fun x : 𝓞 F => ι • x - x)

theorem displacementIdeal_ne_bot {ι : F ≃ₐ[ℚ] F} (hι : ι ≠ 1) :
    displacementIdeal F ι ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_smul_ne_of_ne_one F hι
  intro hbot
  exact hx (sub_eq_zero.mp (Ideal.span_eq_bot.mp hbot _ ⟨x, rfl⟩))

theorem displacementIdeal_le_iff {ι : F ≃ₐ[ℚ] F} {Q : Ideal (𝓞 F)} :
    displacementIdeal F ι ≤ Q ↔ ι ∈ Q.inertia (F ≃ₐ[ℚ] F) := by
  rw [displacementIdeal, Ideal.span_le]
  constructor
  · intro h x
    exact h ⟨x, rfl⟩
  · rintro h - ⟨x, rfl⟩
    exact h x

theorem finite_setOf_inertia_ne_bot :
    {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥}.Finite := by
  have hsub : {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥} ⊆
      ⋃ ι ∈ {ι : F ≃ₐ[ℚ] F | ι ≠ 1},
        {Q : Ideal (𝓞 F) | Q.IsPrime ∧ displacementIdeal F ι ≤ Q} := by
    rintro Q ⟨hQp, -, hQi⟩
    obtain ⟨ι, hιQ, hι1⟩ := (Q.inertia (F ≃ₐ[ℚ] F)).bot_or_exists_ne_one.resolve_left hQi
    refine Set.mem_biUnion (show (ι : F ≃ₐ[ℚ] F) ∈ {ι : F ≃ₐ[ℚ] F | ι ≠ 1} from ?_) ?_
    · simpa using hι1
    · exact ⟨hQp, displacementIdeal_le_iff F |>.mpr hιQ⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Set.toFinite _) ?_) hsub
  intro ι hι
  exact Set.Finite.subset (finite_setOf_isPrime_le F (displacementIdeal_ne_bot F hι))
    fun Q hQ => ⟨hQ.1, hQ.2⟩

omit [NumberField F] in
theorem subsingleton_setOf_prime_natCast_mem {Q : Ideal (𝓞 F)} (hQ : Q ≠ ⊤) :
    {ℓ : ℕ | ℓ.Prime ∧ (ℓ : 𝓞 F) ∈ Q}.Subsingleton := by
  rintro ℓ ⟨hℓ, hℓQ⟩ ℓ' ⟨hℓ', hℓ'Q⟩
  by_contra hne
  apply hQ
  rw [Ideal.eq_top_iff_one]
  have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
  have hbezout : (1 : ℤ) = ℓ * Nat.gcdA ℓ ℓ' + ℓ' * Nat.gcdB ℓ ℓ' := by
    have := Nat.gcd_eq_gcd_ab ℓ ℓ'
    rwa [hcop, Nat.cast_one] at this
  have : (1 : 𝓞 F) = (ℓ : 𝓞 F) * (algebraMap ℤ (𝓞 F) (Nat.gcdA ℓ ℓ')) +
      (ℓ' : 𝓞 F) * (algebraMap ℤ (𝓞 F) (Nat.gcdB ℓ ℓ')) := by
    have := congrArg (algebraMap ℤ (𝓞 F)) hbezout
    push_cast at this ⊢
    simpa using this
  rw [this]
  exact Q.add_mem (Q.mul_mem_right _ hℓQ) (Q.mul_mem_right _ hℓ'Q)

theorem finite_ramifiedPrimes :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥ ∧ (ℓ : 𝓞 F) ∈ Q}.Finite := by
  have hsub : {ℓ : ℕ | ℓ.Prime ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥ ∧ (ℓ : 𝓞 F) ∈ Q} ⊆
      ⋃ Q ∈ {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥},
        {ℓ : ℕ | ℓ.Prime ∧ (ℓ : 𝓞 F) ∈ Q} := by
    rintro ℓ ⟨hℓ, Q, hQp, hQb, hQi, hℓQ⟩
    exact Set.mem_biUnion ⟨hQp, hQb, hQi⟩ ⟨hℓ, hℓQ⟩
  refine Set.Finite.subset (Set.Finite.biUnion (finite_setOf_inertia_ne_bot F) ?_) hsub
  rintro Q ⟨hQp, -, -⟩
  exact (subsingleton_setOf_prime_natCast_mem F hQp.ne_top).finite

end Ramified

theorem exists_pow_pow_eq {G : Type*} [Group G] [Finite G] (σ : G) {k : ℕ}
    (hk : k.Coprime (orderOf σ)) : ∃ m : ℕ, (σ ^ k) ^ m = σ := by
  haveI : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩
  obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective
    (((ZMod.unitOfCoprime k hk)⁻¹ : (ZMod (orderOf σ))ˣ) : ZMod (orderOf σ))
  refine ⟨m, ?_⟩
  rw [← pow_mul]
  conv_rhs => rw [← pow_one σ]
  rw [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [hm, ← ZMod.coe_unitOfCoprime k hk, Units.mul_inv]

theorem exists_prime_notMem_forall_isConj_pow_arithFrobAt
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)],
        Q.under ℤ = Ideal.span {(ℓ : ℤ)} →
        ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  obtain ⟨ℓ, hℓS, hℓ, h⟩ := FrobeniusDensity.statement L σ S
  exact ⟨ℓ, hℓ, hℓS, fun Q _ _ hQ => h Q ‹_› ⟨hQ.symm⟩ ‹_›⟩

section Bridge

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ
  rfl
  rfl
scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _

variable (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
  [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]

omit [IsGalois ℚ F] [IsScalarTower ℚ F (AlgebraicClosure ℚ)] in
theorem inertia_placeIdeal_eq_bot {ℓ : ℕ} (hℓ : ℓ.Prime)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime ℓ)
    (hram : ℓ ∉ (finite_ramifiedPrimes F).toFinset) :
    (placeIdeal A F).inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  by_contra hne
  exact hram ((finite_ramifiedPrimes F).mem_toFinset.mpr ⟨hℓ, placeIdeal A F, inferInstance,
    placeIdeal_ne_bot A F hℓ hA, hne, natCast_mem_placeIdeal A F hA⟩)

theorem exists_of_ker_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (S : Finset ℕ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n k : ℕ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H ∧ g * τ * g⁻¹ * (σ ^ k)⁻¹ ∈ H := by

  obtain ⟨ℓ, hℓ, hℓmem, hQ⟩ :=
    exists_prime_notMem_forall_isConj_pow_arithFrobAt F
      (AlgEquiv.restrictNormalHom F σ) (S ∪ (finite_ramifiedPrimes F).toFinset)
  rw [Finset.mem_union, not_or] at hℓmem
  obtain ⟨hℓS, hℓram⟩ := hℓmem

  obtain ⟨A, hA⟩ := exists_liesOverPrime (AlgebraicClosure ℚ) hℓ
  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA

  have hτF : IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) (placeIdeal A F) :=
    isArithFrobAt_restrictNormalHom_of_isFrobeniusAt F A hℓ hA hτ
  haveI hfin : Finite ((𝓞 F) ⧸ placeIdeal A F) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (placeIdeal_ne_bot A F hℓ hA)
  obtain ⟨k, hk, hconj⟩ := hQ (placeIdeal A F) (placeIdeal_under_eq A F hℓ hA)

  have hτeq : AlgEquiv.restrictNormalHom F τ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) (placeIdeal A F) := by
    have hmem := hτF.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F)
      (placeIdeal A F))
    rw [inertia_placeIdeal_eq_bot F hℓ hA hℓram, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  rw [← hτeq] at hconj

  obtain ⟨c, hc⟩ := isConj_iff.mp hconj

  obtain ⟨m, hm⟩ := exists_pow_pow_eq (AlgEquiv.restrictNormalHom F σ) hk
  have hcm : c * AlgEquiv.restrictNormalHom F σ * c⁻¹ = (AlgEquiv.restrictNormalHom F τ) ^ m := by
    rw [← hc, conj_pow, hm]

  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) c⁻¹
  refine ⟨ℓ, A, τ, g, m, k, hℓ, hℓS, hA, hτ, hker ?_, hker ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_pow, map_inv, map_inv, hg, ← hcm]
    group
  · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hg, ← hc]
    group

end Bridge

section Open

theorem main
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n k : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H ∧ g * τ * g⁻¹ * (σ ^ k)⁻¹ ∈ H := by

  have hnhds : (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ nhds 1 :=
    hH.mem_nhds H.one_mem
  obtain ⟨E, hEfin, hEnormal, hEH⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) H).mp hnhds

  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ E) = E.algebra := Subsingleton.elim _ _
  haveI hN : @Normal ℚ E _ _ DivisionRing.toRatAlgebra := by rw [halg]; exact hEnormal
  haveI hFD : @FiniteDimensional ℚ E _ _ DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hEfin
  haveI : NumberField E := @NumberField.mk _ _ inferInstance hFD
  haveI : IsGalois ℚ E := ⟨⟩
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker ≤ H := by
    intro x hx
    apply hEH
    haveI := hEnormal
    rw [← IntermediateField.restrictNormalHom_ker E, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hx
    convert hx
    rfl
  obtain ⟨ℓ, A, τ, g, n, k, hℓ, hℓS, hA, hτ, hmem, hmem'⟩ :=
    exists_of_ker_le E hker σ M.primeFactors
  refine ⟨ℓ, A, τ, g, n, k, hℓ, ?_, hA, hτ, hmem, hmem'⟩
  intro hdvd
  exact hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hM.ne'⟩)

end Open

end P2C0DivDensity
p2m_reactivate "P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen.P2C0DivDensity"

end
p2m_reactivate "P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen.P2C0DivDensity"

theorem solution
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n k : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H ∧ g * τ * g⁻¹ * (σ ^ k)⁻¹ ∈ H :=
  P2C0DivDensity.main H hH σ hM

end S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
end P2MW
export P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen (solution)
