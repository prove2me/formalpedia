-- Prove2me | solution 1 for ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5907a9e3-839c-557d-b501-b715e39b48bf

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
import Theorems.Thm_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
import Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S
import Theorems.Thm_groupCohomology_mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1S
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.sizeOf_spec TaylorWiles.CyclotomicLevelStructure.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe"

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation IntermediateField

noncomputable section

namespace P2mTW1S

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ
  rfl
  rfl

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

private lemma _root_.P2mTW1S.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "P2mTW1S" "exists_isPrimitiveRoot"
section Main

variable {k : Type} [Field k]

lemma two_ne_zero_of_charP (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p] : (2 : k) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

variable {p : ℕ} [Fact p.Prime] {ρbar : ResidualGaloisRep k}
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  {ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (LinearMap.ker (LinearMap.trace k ρbar.V))}

lemma rho0_eq_one (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ} (hg : ρbar.ρ g = 1) :
    ρ₀ g = 1 := by
  have hg' : ρbar.ρ g⁻¹ = 1 := by
    have : ρbar.ρ g⁻¹ * ρbar.ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hg, mul_one] at this
  apply LinearMap.ext
  intro v
  rw [hρ₀ g v, Module.End.one_apply]
  apply Subtype.ext
  rw [ResidualGaloisRep.adZeroRep_apply_coe, hg, hg', one_mul, mul_one]

lemma dualTwist_ρ_eq_one {g : Γ} (h1 : ρ₀ g⁻¹ = 1) (h2 : cycloChar p g = 1) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ g = 1 := by
  ext f v
  rw [Rep.dualTwist_ρ_apply]
  simp [h1, h2]

lemma hsm' (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) :
    ∀ f : ((Rep.of ρ₀).dualTwist (cycloChar p)),
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ s f = f := by
  classical
  intro f
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hLfd
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hζint : IsIntegral ℚ ζ := (isIntegral_algebraicClosure_rat).isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hζint
  refine ⟨L ⊔ ℚ⟮ζ⟯, finiteDimensional_sup L ℚ⟮ζ⟯, fun s hs => ?_⟩
  have hsL : ∀ x ∈ L, s x = x := fun x hx =>
    (mem_fixingSubgroup_iff (K := L ⊔ ℚ⟮ζ⟯) s).mp hs x (le_sup_left (a := L) hx)
  have hsζ : s ζ = ζ :=
    (mem_fixingSubgroup_iff (K := L ⊔ ℚ⟮ζ⟯) s).mp hs ζ
      (le_sup_right (a := L) (mem_adjoin_simple_self ℚ ζ))
  have hρs : ρbar.ρ s = 1 := hL s hsL
  have hρs' : ρbar.ρ s⁻¹ = 1 := by
    have : ρbar.ρ s⁻¹ * ρbar.ρ s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hρs, mul_one] at this
  have h1 : ρ₀ s⁻¹ = 1 := rho0_eq_one hρ₀ hρs'
  have h2 : cycloChar p s = 1 := cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p s hζ hsζ
  rw [dualTwist_ρ_eq_one h1 h2]
  rfl

lemma hMur' (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) (S : Finset Nat.Primes)
    (hpS : pPrime p ∈ S) (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q) :
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ,
        ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ g = 1 := by
  intro q hq A hA g hg
  have hp : p.Prime := Fact.out
  have hqp : ¬ (q : ℕ) ∣ p := by
    intro hdvd
    have : (q : ℕ) = p := (Nat.prime_dvd_prime_iff_eq q.2 hp).mp hdvd
    apply hq
    have hq' : q = pPrime p := Subtype.ext this
    rw [hq']; exact hpS
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hgζ : g ζ = ζ :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A q.2 hA hg hqp
      hζ.pow_eq_one
  have h2 : cycloChar p g = 1 := cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p g hζ hgζ
  have hg' : g⁻¹ ∈ A.inertiaSubgroupIn ℚ := inv_mem hg
  have h1 : ρ₀ g⁻¹ = 1 := rho0_eq_one hρ₀ (hur q hq A hA g⁻¹ hg')
  exact dualTwist_ρ_eq_one h1 h2

lemma finiteDimensional_dualTwist [Finite k] :
    FiniteDimensional (ZMod p) ((Rep.of ρ₀).dualTwist (cycloChar p)) := by
  haveI : Finite (LinearMap.ker (LinearMap.trace k ρbar.V)) := Module.finite_of_finite k
  haveI : Module.Finite (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
    Module.Finite.of_finite
  change FiniteDimensional (ZMod p)
    (Module.Dual (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V)))
  infer_instance

end Main

theorem main
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q)
    (n : ℕ) (T : Finset ℕ) :
    ∃ Q : Finset Nat.Primes,
      Q.card = Module.finrank (ZMod p)
        (continuousH1S S ((Rep.of ρ₀).dualTwist (cycloChar p))) ∧
      (∀ q ∈ Q, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
            ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      ∀ x ∈ continuousH1S (S ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)),
        (∀ q ∈ Q, (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom x = 0) →
        x = 0 := by
  classical
  set M' : Rep (ZMod p) Γ := (Rep.of ρ₀).dualTwist (cycloChar p) with hM'
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_charP p hp2
  haveI : FiniteDimensional (ZMod p) M' := finiteDimensional_dualTwist

  haveI : FiniteDimensional (ZMod p) (continuousH1S S M') :=
    finiteDimensional_continuousH1S S M' (hsm' hρ₀)

  let good : Set Nat.Primes := {q | (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧
    ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)}

  let f : ∀ q : Nat.Primes, H1 M' →ₗ[ZMod p] H1 (Rep.res (primeLocalToGlobal q) M') :=
    fun q => (groupCohomology.map (primeLocalToGlobal q)
      (𝟙 (Rep.res (primeLocalToGlobal q) M')) 1).hom

  have hpad : ∀ T' : Finset Nat.Primes, ∃ q ∈ good, q ∉ T' := by
    intro T'
    obtain ⟨q, hq, hqS, hmod, hunr, hfrob⟩ :=
      ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible h2 ρbar habs
        hsplit p hp2 n (T ∪ T'.image (fun q : Nat.Primes => (q : ℕ)))
    refine ⟨⟨q, hq⟩, ⟨fun h => hqS (Finset.mem_union_left _ h), hmod, hunr, hfrob⟩, fun h => hqS ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨q, hq⟩, h, rfl⟩)

  have hkill : ∀ ψ ∈ continuousH1S S M', ψ ≠ 0 → ∀ T' : Finset Nat.Primes,
      ∃ q ∈ good, q ∉ T' ∧ f q ψ ≠ 0 := by
    intro ψ hψ hψ0 T'
    obtain ⟨q, hqT, hmod, hunr, hfrob, hne⟩ :=
      ResidualGaloisRep.exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S p hp2 ρbar habs
        hsplit hTW ρ₀ hρ₀ S ψ hψ hψ0 n (T ∪ T'.image (fun q : Nat.Primes => (q : ℕ)))
    refine ⟨q, ⟨fun h => hqT (Finset.mem_union_left _ h), hmod, hunr, hfrob⟩, fun h => hqT ?_, hne⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, h, rfl⟩)

  obtain ⟨Q, hQgood, -, hcard, hkilled⟩ :=
    Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
      f (continuousH1S S M') good hpad hkill ∅
  refine ⟨Q, hcard, fun q hq => hQgood hq, fun x hx h0 => ?_⟩

  have hxS : x ∈ continuousH1S S M' :=
    groupCohomology.mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero S Q M'
      (hsm' hρ₀) (hMur' hρ₀ S hpS hur) x hx h0
  exact hkilled x hxS h0

end P2mTW1S
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist.P2mTW1S"

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q)
    (n : ℕ) (T : Finset ℕ) :
    ∃ Q : Finset Nat.Primes,
      Q.card = Module.finrank (ZMod p)
        (continuousH1S S ((Rep.of ρ₀).dualTwist (cycloChar p))) ∧
      (∀ q ∈ Q, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
            ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      ∀ x ∈ continuousH1S (S ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)),
        (∀ q ∈ Q, (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom x = 0) →
        x = 0 :=
  P2mTW1S.main p hp2 ρbar habs hsplit hTW ρ₀ hρ₀ S hpS hur n T

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist.P2mTW1S"

end S_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
end P2MW
export P2MW.S_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist (solution)
