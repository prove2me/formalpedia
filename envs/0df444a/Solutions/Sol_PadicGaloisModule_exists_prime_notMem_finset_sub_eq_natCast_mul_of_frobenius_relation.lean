-- Prove2me | solution 1 for PadicGaloisModule.exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1c05726a-f131-5865-b15b-da01111ed530

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open scoped Pointwise

namespace RibetRedundancyEngine

section Saturation

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]

def saturation (r : R) (Λ : Submodule R E) : Submodule R E where
  carrier := {ψ | ∃ n : ℕ, r ^ n • ψ ∈ Λ}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [smul_add, pow_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ ha
    · rw [mul_smul]; exact Λ.smul_mem _ hb
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [smul_comm]
    exact Λ.smul_mem _ ha

theorem mem_saturation_iff (r : R) (Λ : Submodule R E) (ψ : E) :
    ψ ∈ saturation r Λ ↔ ∃ n : ℕ, r ^ n • ψ ∈ Λ :=
  Iff.rfl

variable [IsNoetherianRing R] [Module.Finite R E]

theorem exists_pow_smul_mem_of_exists_pow_smul_mem (r : R) (Λ : Submodule R E) :
    ∃ N : ℕ, ∀ ψ : E, (∃ n : ℕ, r ^ n • ψ ∈ Λ) → r ^ N • ψ ∈ Λ := by
  haveI : IsNoetherian R E := isNoetherian_of_isNoetherianRing_of_finite R E
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (saturation r Λ)
  have hmem : ∀ ψ ∈ s, ∃ n : ℕ, r ^ n • ψ ∈ Λ := fun ψ hψ =>
    (mem_saturation_iff r Λ ψ).mp (hs ▸ Submodule.subset_span hψ)
  choose! n hn using hmem
  refine ⟨∑ ψ ∈ s, n ψ, fun ψ hψ => ?_⟩
  have hψ' : ψ ∈ Submodule.span R (s : Set E) := by
    rw [hs]; exact (mem_saturation_iff r Λ ψ).mpr hψ
  clear hψ
  induction hψ' using Submodule.span_induction with
  | mem x hx =>
      have hle : n x ≤ ∑ ψ ∈ s, n ψ :=
        Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_coe.mp hx)
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
      rw [hc, add_comm, pow_add, mul_smul]
      exact Λ.smul_mem _ (hn x (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Λ.smul_mem _ hx

end Saturation

section Divide

variable {R : Type*} [CommRing R] [IsDomain R] {A : Type*} [AddCommGroup A] [Module R A]
  [Module.IsTorsionFree R A]

theorem exists_smul_eq_of_forall_exists (c : R) (hc : c ≠ 0) (δ : Module.End R A)
    (h : ∀ a : A, ∃ b : A, δ a = c • b) : ∃ ψ : Module.End R A, c • ψ = δ := by
  choose b hb using h
  have hinj : Function.Injective fun x : A => c • x := smul_right_injective A hc
  refine ⟨{ toFun := b, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply hinj
    simp only [smul_add, ← hb, map_add]
  · intro a x
    apply hinj
    simp only [RingHom.id_apply, ← hb, map_smul]
    rw [smul_comm, ← hb]
  · ext a
    simp [hb]

end Divide

section Conj

variable {R : Type*} [CommSemiring R] {E : Type*} [Ring E] [Module R E] [SMulCommClass R E E]
  [IsScalarTower R E E]

theorem relation_of_conj {a b e u u' x y : E} {c : R}
    (hy : y = u' * x * u) (huu' : u * u' = 1) (hu'u : u' * u = 1)
    (ha : u * a = a * u) (hb : u * b = b * u) (he : u * e = e * u)
    (hrel : a * y = b * (y * y) + c • e) :
    a * x = b * (x * x) + c • e := by
  have hx : u * y * u' = x := by
    rw [hy]; simp only [← mul_assoc]; rw [huu', one_mul, mul_assoc, huu', mul_one]
  have h1 : u * (a * y) * u' = a * x := by
    rw [← hx]; simp only [← mul_assoc]; rw [ha]
  have h2 : u * (y * y) * u' = x * x := by
    rw [← hx]
    calc u * (y * y) * u' = u * y * 1 * y * u' := by simp only [mul_one, mul_assoc]
      _ = u * y * (u' * u) * y * u' := by rw [hu'u]
      _ = u * y * u' * (u * y * u') := by simp only [mul_assoc]
  have h3 : u * (b * (y * y) + c • e) * u' = b * (x * x) + c • e := by
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ← h2]
    congr 1
    · simp only [← mul_assoc]; rw [hb]
    · rw [he, mul_assoc, huu', mul_one]
  rw [← h1, hrel, h3]

end Conj

section Main

theorem map_mem_smul_top {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A] [Module R A]
    (f : Module.End R A) (c : R) {x : A} (hx : x ∈ c • (⊤ : Submodule R A)) :
    f x ∈ c • (⊤ : Submodule R A) := by
  obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c ⊤).mp hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem map_sub_mem_smul_top {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A] [Module R A]
    (f : Module.End R A) (c : R) {x y : A} (hx : x - y ∈ c • (⊤ : Submodule R A)) :
    f x - f y ∈ c • (⊤ : Submodule R A) := by
  rw [← map_sub]; exact map_mem_smul_top f c hx

theorem exists_frobenius_conj_fixing (L' : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L'] (S : Finset ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ P.LiesOverPrime ℓ ∧ P.IsFrobeniusAt τ ℓ ∧
        ∀ x ∈ L', (g * τ * g⁻¹ * σ⁻¹) x = x := by
  have hopen : IsOpen ((L'.fixingSubgroup : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    IntermediateField.fixingSubgroup_isOpen L'
  have hnhds : ((L'.fixingSubgroup : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ nhds 1 :=
    hopen.mem_nhds (Subgroup.one_mem _)
  obtain ⟨E, hEfin, hEnormal, hEH⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) _).mp hnhds

  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ E) = E.algebra := Subsingleton.elim _ _
  haveI hN : @Normal ℚ E _ _ DivisionRing.toRatAlgebra := by rw [halg]; exact hEnormal
  haveI hFD : @FiniteDimensional ℚ E _ _ DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hEfin
  haveI : NumberField E := @NumberField.mk _ _ inferInstance hFD
  haveI : IsGalois ℚ E := ⟨⟩
  obtain ⟨ℓ, P, τ, g, hℓ, hℓS, hP, hτ, hker⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker E
      (H := (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker) le_rfl S σ
  refine ⟨ℓ, P, τ, g, hℓ, hℓS, hP, hτ, ?_⟩
  have hfixE : g * τ * g⁻¹ * σ⁻¹ ∈ (E.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    haveI := hEnormal
    rw [← IntermediateField.restrictNormalHom_ker E, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hker
    convert hker
    rfl
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hEH hfixE)

theorem main
    {𝕋 : Type} [Ring 𝕋] (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    {A : Type} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
    (φ : 𝕋 →+* Module.End ℤ_[p] A)
    (hφ : ∀ t : 𝕋, φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
      ∃ t' : 𝕋, t = (p : 𝕋) * t')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋), ρ σ * φ t = φ t * ρ σ)
    (hcont : ∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A))
    (T : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → 𝕋) (e₁ e₂ : ZMod M → 𝕋) (w : ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          φ (T ℓ hℓ hℓM) * ρ σ =
            φ (e₁ (ℓ : ZMod M)) * (ρ σ * ρ σ) + ((ℓ : ℤ_[p]) ^ w) • φ (e₂ (ℓ : ZMod M)))
    (S : Finset ℕ) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀M : ¬ ℓ₀ ∣ M) (hℓ₀p : ℓ₀ ≠ p) :
    ∃ (q : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M), q ∉ S ∧ q ≠ p ∧ (q : ZMod M) = (ℓ₀ : ZMod M) ∧
      ∃ t' : 𝕋, T ℓ₀ hℓ₀ hℓ₀M - T q hq hqM = (p : 𝕋) * t' := by
  classical
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hM0 : M ≠ 0 := NeZero.ne M

  set Λ : Submodule ℤ_[p] (Module.End ℤ_[p] A) := Submodule.span ℤ_[p] (Set.range φ) with hΛ
  haveI : Module.Finite ℤ_[p] (Module.End ℤ_[p] A) := Module.Finite.linearMap ℤ_[p] ℤ_[p] A A
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_of_exists_pow_smul_mem (p : ℤ_[p]) Λ

  obtain ⟨L, hLfin, hL⟩ := hcont (N + 1)
  haveI := hLfin
  set n₀ : ℕ := M * p ^ (N + 1) with hn₀
  have hn₀pos : 0 < n₀ := Nat.pos_of_ne_zero (mul_ne_zero hM0 (pow_ne_zero _ hpp.ne_zero))
  haveI : NeZero n₀ := ⟨hn₀pos.ne'⟩
  obtain ⟨ζ, hζroot⟩ : ∃ ζ : AlgebraicClosure ℚ, (Polynomial.cyclotomic n₀ (AlgebraicClosure ℚ)).IsRoot ζ := by
    apply IsAlgClosed.exists_root
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hn₀pos).ne'
  have hζ : IsPrimitiveRoot ζ n₀ := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn₀pos.ne'
  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral hn₀pos).tower_top
  set L' : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {ζ} with hL'
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.adjoin.finiteDimensional hζint
  haveI : FiniteDimensional ℚ L' := IntermediateField.finiteDimensional_sup L _
  have hLL' : L ≤ L' := le_sup_left
  have hζL' : ζ ∈ L' :=
    (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ L') (IntermediateField.mem_adjoin_simple_self ℚ ζ)

  obtain ⟨A₀, σ₀, hA₀, hσ₀⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨ℓ₀, hℓ₀⟩
  set S' : Finset ℕ := S ∪ M.primeFactors ∪ {p} with hS'
  obtain ⟨q, P, τ, g, hq, hqS', hP, hτ, hfixL'⟩ := exists_frobenius_conj_fixing L' S' σ₀
  have hqS : q ∉ S := fun h => hqS' (by simp [hS', h])
  have hqp : q ≠ p := fun h => hqS' (by simp [hS', h])
  have hqM : ¬ q ∣ M := fun h => hqS' (by
    have : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, h, hM0⟩
    simp [hS', this])

  set h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := g * τ * g⁻¹ * σ₀⁻¹ with hh
  have hfix : ∀ x ∈ L', h x = x := hfixL'
  have hgτ : g * τ * g⁻¹ = h * σ₀ := by rw [hh]; group
  have hτ_eq : τ = g⁻¹ * (h * σ₀) * g := by rw [← hgτ]; group

  have hndvd : ∀ {r : ℕ}, r.Prime → ¬ r ∣ M → r ≠ p → ¬ r ∣ n₀ := by
    intro r hr hrM hrp hdiv
    rcases (Nat.Prime.dvd_mul hr).mp hdiv with h1 | h2
    · exact hrM h1
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow h2))
  have hζpow : ζ ^ n₀ = 1 := hζ.pow_eq_one
  have hσ₀ζ : σ₀ ζ = ζ ^ ℓ₀ :=
    ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one A₀ hℓ₀ hA₀ hσ₀ (hndvd hℓ₀ hℓ₀M hℓ₀p) hζpow
  have hτζ : τ (g⁻¹ ζ) = (g⁻¹ ζ) ^ q :=
    ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one P hq hP hτ (hndvd hq hqM hqp)
      (by rw [← map_pow, hζpow, map_one])
  have hζq : ζ ^ q = ζ ^ ℓ₀ := by
    have e1 : (g * τ * g⁻¹) ζ = ζ ^ q := by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτζ, map_pow, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have e2 : (h * σ₀) ζ = ζ ^ ℓ₀ := by
      rw [AlgEquiv.mul_apply, hσ₀ζ, map_pow, hfix ζ hζL']
    rw [← e1, ← e2, hgτ]
  have hmod : ℓ₀ ≡ q [MOD n₀] := by
    rw [Nat.modEq_iff_dvd]
    apply (hζ.zpow_eq_one_iff_dvd _).mp
    rw [zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, hζq, div_self (pow_ne_zero _ hζ0)]
  have hmodM : ℓ₀ ≡ q [MOD M] := Nat.ModEq.of_mul_right (p ^ (N + 1)) hmod
  have hmodp : ℓ₀ ^ w ≡ q ^ w [MOD p ^ (N + 1)] :=
    (Nat.ModEq.of_dvd (dvd_mul_left (p ^ (N + 1)) M) hmod).pow w
  have hcast : (q : ZMod M) = (ℓ₀ : ZMod M) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodM.symm
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], ((q : ℤ_[p]) ^ w) - ((ℓ₀ : ℤ_[p]) ^ w) = (p : ℤ_[p]) ^ (N + 1) * c := by
    obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.mp hmodp
    refine ⟨(c : ℤ_[p]), ?_⟩
    have := congrArg (Int.cast : ℤ → ℤ_[p]) hc
    push_cast at this
    exact this

  have relℓ₀ := hES ℓ₀ hℓ₀ hℓ₀M hℓ₀p A₀ hA₀ σ₀ hσ₀
  have relq₀ := hES q hq hqM hqp P hP τ hτ
  rw [hcast] at relq₀
  have relq : φ (T q hq hqM) * ρ (h * σ₀) =
      φ (e₁ (ℓ₀ : ZMod M)) * (ρ (h * σ₀) * ρ (h * σ₀)) + ((q : ℤ_[p]) ^ w) • φ (e₂ (ℓ₀ : ZMod M)) := by
    refine relation_of_conj (u := ρ g) (u' := ρ g⁻¹) (y := ρ τ) ?_ ?_ ?_ (hcomm g _) (hcomm g _)
      (hcomm g _) relq₀
    · rw [← map_mul, ← map_mul, ← hτ_eq]
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]

  set Nd : Submodule ℤ_[p] A := ((p : ℤ_[p]) ^ (N + 1)) • (⊤ : Submodule ℤ_[p] A) with hNd
  have hNd_eq : Ideal.span {(p : ℤ_[p])} ^ (N + 1) • (⊤ : Submodule ℤ_[p] A) = Nd := by
    rw [hNd, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  have hhfix : ∀ a : A, ρ h a - a ∈ Nd := by
    intro a
    rw [← hNd_eq]
    exact hL h (fun x hx => hfix x (hLL' hx)) a
  set X : Module.End ℤ_[p] A := ρ (h * σ₀) with hX
  set s : Module.End ℤ_[p] A := ρ σ₀ with hs
  have hX1 : ∀ a : A, X a - s a ∈ Nd := by
    intro a
    rw [hX, hs, map_mul, Module.End.mul_apply]
    exact hhfix _
  have hX2 : ∀ a : A, X (X a) - s (s a) ∈ Nd := by
    intro a
    have e : X (X a) - s (s a) = (X (X a) - s (X a)) + (s (X a) - s (s a)) := by abel
    rw [e]
    exact Nd.add_mem (hX1 _) (map_sub_mem_smul_top s _ (hX1 a))
  have hdiff : ∀ a : A, (φ (T ℓ₀ hℓ₀ hℓ₀M) - φ (T q hq hqM)) (s a) ∈ Nd := by
    intro a
    have r1 := LinearMap.congr_fun relℓ₀ a
    have r2 := LinearMap.congr_fun relq a
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at r1 r2
    have e : (φ (T ℓ₀ hℓ₀ hℓ₀M) - φ (T q hq hqM)) (s a) =
        (φ (e₁ (ℓ₀ : ZMod M)) (s (s a)) - φ (e₁ (ℓ₀ : ZMod M)) (X (X a)))
        + (φ (T q hq hqM) (X a) - φ (T q hq hqM) (s a))
        - (((q : ℤ_[p]) ^ w) - ((ℓ₀ : ℤ_[p]) ^ w)) • φ (e₂ (ℓ₀ : ZMod M)) a := by
      rw [LinearMap.sub_apply, r1, r2, sub_smul]
      abel
    rw [e]
    refine Nd.sub_mem (Nd.add_mem ?_ ?_) ?_
    · rw [← neg_sub]
      exact Nd.neg_mem (map_sub_mem_smul_top (φ (e₁ (ℓ₀ : ZMod M))) _ (hX2 a))
    · exact map_sub_mem_smul_top _ _ (hX1 a)
    · rw [hc, mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

  set δ : Module.End ℤ_[p] A := φ (T ℓ₀ hℓ₀ hℓ₀M) - φ (T q hq hqM) with hδ
  have hδall : ∀ b : A, δ b ∈ Nd := by
    intro b
    have hb : s (ρ σ₀⁻¹ b) = b := by
      rw [hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have := hdiff (ρ σ₀⁻¹ b)
    rwa [hb] at this

  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.End ℤ_[p] A, ((p : ℤ_[p]) ^ (N + 1)) • ψ = δ := by
    apply exists_smul_eq_of_forall_exists _ (pow_ne_zero _ hp0)
    intro a
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hδall a)
    exact ⟨b, hb.symm⟩
  have hδΛ : δ ∈ Λ := Λ.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hψN : (p : ℤ_[p]) ^ N • ψ ∈ Λ := hN ψ ⟨N + 1, by rw [hψ]; exact hδΛ⟩
  have hδp : δ ∈ Ideal.span {(p : ℤ_[p])} • Λ := by
    rw [Submodule.ideal_span_singleton_smul, ← hψ, pow_succ', mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hψN
  have hmem : φ (T ℓ₀ hℓ₀ hℓ₀M - T q hq hqM) ∈ Ideal.span {(p : ℤ_[p])} • Λ := by
    rw [map_sub]; exact hδp
  obtain ⟨t', ht'⟩ := hφ _ hmem
  exact ⟨q, hq, hqM, hqS, hqp, hcast, t', ht'⟩

end Main

end RibetRedundancyEngine

theorem solution
    {𝕋 : Type} [Ring 𝕋] (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    {A : Type} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
    (φ : 𝕋 →+* Module.End ℤ_[p] A)
    (hφ : ∀ t : 𝕋, φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
      ∃ t' : 𝕋, t = (p : 𝕋) * t')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋), ρ σ * φ t = φ t * ρ σ)
    (hcont : ∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A))
    (T : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → 𝕋) (e₁ e₂ : ZMod M → 𝕋) (w : ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          φ (T ℓ hℓ hℓM) * ρ σ =
            φ (e₁ (ℓ : ZMod M)) * (ρ σ * ρ σ) + ((ℓ : ℤ_[p]) ^ w) • φ (e₂ (ℓ : ZMod M)))
    (S : Finset ℕ) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀M : ¬ ℓ₀ ∣ M) (hℓ₀p : ℓ₀ ≠ p) :
    ∃ (q : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M), q ∉ S ∧ q ≠ p ∧ (q : ZMod M) = (ℓ₀ : ZMod M) ∧
      ∃ t' : 𝕋, T ℓ₀ hℓ₀ hℓ₀M - T q hq hqM = (p : 𝕋) * t' :=
  RibetRedundancyEngine.main p M φ hφ ρ hcomm hcont T e₁ e₂ w hES S ℓ₀ hℓ₀ hℓ₀M hℓ₀p

end S_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
end P2MW
export P2MW.S_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation (solution)
