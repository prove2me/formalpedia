-- Prove2me | solution 1 for ResidualGaloisRep.exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0bbddba1-3830-5b92-88a2-600df53fc133

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range
import Theorems.Thm_ResidualGaloisRep_eq_zero_of_forall_map_adZeroRep_eq_smul
import Theorems.Thm_Rep_dualTwist_of_invariants_eq_bot_of_forall_linearMap_eq_zero
import Theorems.Thm_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
p2m_attr_erase "simp" "ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation IntermediateField

noncomputable section

namespace P2mInjRes

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := by
  have h := @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ)
    (AlgebraicClosure.instIsAlgClosure ℚ)
  convert h
  rfl

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
  Algebra.IsAlgebraic.isIntegral

private lemma _root_.P2mInjRes.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "P2mInjRes" "exists_isPrimitiveRoot"

lemma two_ne_zero_of_charP (k : Type) [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP k p] : (2 : k) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

lemma exists_apply_eq_pow {N : ℕ} (hN : 0 < N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ N) (σ : Γ) :
    ∃ i : ℕ, σ ζ = ζ ^ i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h1 : (σ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨i, hi.symm⟩

lemma apply_apply_comm {N : ℕ} (hN : 0 < N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ N) (σ τ : Γ) :
    σ (τ ζ) = τ (σ ζ) := by
  obtain ⟨i, hi⟩ := exists_apply_eq_pow hN hζ σ
  obtain ⟨j, hj⟩ := exists_apply_eq_pow hN hζ τ
  rw [hj, map_pow, hi, map_pow, hj, ← pow_mul, ← pow_mul, mul_comm]

lemma commutator_apply_eq {N : ℕ} (hN : 0 < N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ N) (g x : Γ) :
    (g * x * g⁻¹ * x⁻¹) ζ = ζ := by
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, apply_apply_comm hN hζ g⁻¹ x⁻¹,
    AlgEquiv.mul_apply, ← AlgEquiv.mul_apply x, mul_inv_cancel, AlgEquiv.one_apply,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

lemma cycloChar_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (cycloChar p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot p

  let K : IntermediateField ℚ Qb := ℚ⟮ξ⟯
  haveI : Algebra.IsIntegral ℚ Qb := isIntegral_algebraicClosure_rat
  haveI hK : IsCyclotomicExtension {p} ℚ K :=
    hξ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.pos
  set z : K := IsCyclotomicExtension.zeta p ℚ K with hzdef
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K

  have hμ : IsPrimitiveRoot (z ^ (a : ZMod p).val) p :=
    hz.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  let τ : K ≃ₐ[ℚ] K := IsCyclotomicExtension.fromZetaAut hμ hirr
  have hτz : τ z = z ^ (a : ZMod p).val := IsCyclotomicExtension.fromZetaAut_spec hμ hirr

  let σ : Γ := AlgEquiv.liftNormal τ Qb
  have hz' : IsPrimitiveRoot (z : Qb) p :=
    hz.map_of_injective (f := algebraMap K Qb) (algebraMap K Qb).injective
  have hσz : σ (z : Qb) = (z : Qb) ^ (a : ZMod p).val := by
    have h := AlgEquiv.liftNormal_commutes τ Qb z
    rw [hτz] at h
    rw [show ((z : Qb)) = algebraMap K Qb z from rfl, h, map_pow]
  refine ⟨σ, ?_⟩

  have hspec : σ (z : Qb) = (z : Qb) ^ ((cycloChar p σ : (ZMod p)ˣ) : ZMod p).val := by
    have hu : (hz'.toRootsOfUnity : Qbˣ) ∈ rootsOfUnity p Qb := (hz'.toRootsOfUnity).2
    have h := modularCyclotomicCharacter.spec Qb (card_rootsOfUnity_eq_self p)
      (σ : Qb ≃+* Qb) hu
    have hcoe : ((hz'.toRootsOfUnity : Qbˣ) : Qb) = (z : Qb) := hz'.val_toRootsOfUnity_coe
    rw [hcoe] at h
    exact h
  rw [hσz] at hspec
  have hval := hz'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hspec
  ext
  exact (ZMod.val_injective p hval).symm

lemma finite_range_rho {k : Type} [Field k] (ρbar : ResidualGaloisRep k) :
    (Set.range ρbar.ρ).Finite := by
  classical
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hLfd

  let b := Module.finBasis ℚ L
  let f : Γ → (Fin (Module.finrank ℚ L) → Qb) := fun σ i => σ (b i : Qb)
  have hint : ∀ i, IsIntegral ℚ ((b i : L) : Qb) := fun i =>
    isIntegral_algebraicClosure_rat.isIntegral _
  have hf : Set.range f ⊆ Set.pi Set.univ (fun i => (minpoly ℚ ((b i : L) : Qb)).rootSet Qb) := by
    rintro _ ⟨σ, rfl⟩ i -
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero (hint i), ?_⟩
    change aeval (σ ((b i : L) : Qb)) (minpoly ℚ ((b i : L) : Qb)) = 0
    rw [aeval_algEquiv, AlgHom.coe_comp, Function.comp_apply, minpoly.aeval, map_zero]
  have hffin : (Set.range f).Finite :=
    (Set.Finite.pi (fun i => rootSet_finite _ _) : (Set.pi Set.univ _).Finite).subset hf

  have hdep : ∀ σ τ : Γ, f σ = f τ → ρbar.ρ σ = ρbar.ρ τ := by
    intro σ τ hστ
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hb : ∀ i, (τ⁻¹ * σ) (b i : Qb) = (b i : Qb) := by
        intro i
        have := congrFun hστ i
        simp only [f] at this
        rw [AlgEquiv.mul_apply, this, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

      have hx' : (⟨x, hx⟩ : L) = ∑ i, b.repr ⟨x, hx⟩ i • b i := (b.sum_repr ⟨x, hx⟩).symm
      have hxQ : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : L) : Qb) := by
        have := congrArg (fun y : L => (y : Qb)) hx'
        dsimp only at this
        rw [IntermediateField.coe_sum] at this
        refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
        exact IntermediateField.coe_smul _ _ _
      rw [hxQ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hb i]
    have h1 : ρbar.ρ (τ⁻¹ * σ) = 1 := hL _ hfix
    have : ρbar.ρ τ * ρbar.ρ (τ⁻¹ * σ) = ρbar.ρ σ := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [h1, mul_one] at this
    exact this.symm
  haveI : Finite (Set.range f) := hffin.to_subtype
  let g : Set.range f → Module.End k ρbar.V := fun t => ρbar.ρ t.2.choose
  have hg : ∀ σ : Γ, ρbar.ρ σ = g ⟨f σ, σ, rfl⟩ := by
    intro σ
    have hspec : f (⟨f σ, σ, rfl⟩ : Set.range f).2.choose = f σ := (⟨f σ, σ, rfl⟩ : Set.range f).2.choose_spec
    exact hdep σ _ hspec.symm
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, (hg σ).symm⟩

section Dual

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] {ρbar : ResidualGaloisRep k}
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  {ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (LinearMap.ker (LinearMap.trace k ρbar.V))}

lemma rho0_eq_one_of_adZeroRep (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ}
    (hg : ρbar.adZeroRep g = 1) : ρ₀ g = 1 := by
  apply LinearMap.ext
  intro v
  rw [hρ₀ g v, hg]
  rfl

lemma adZeroRep_eq_one_of_rho0 (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ}
    (hg : ρ₀ g = 1) : ρbar.adZeroRep g = 1 := by
  apply LinearMap.ext
  intro v
  rw [← hρ₀ g v, hg]
  rfl

lemma adZeroRep_eq_one_of_rho (g : Γ) (hg : ρbar.ρ g = 1) : ρbar.adZeroRep g = 1 := by
  have hg' : ρbar.ρ g⁻¹ = 1 := by
    have : ρbar.ρ g⁻¹ * ρbar.ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hg, mul_one] at this
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [ResidualGaloisRep.adZeroRep_apply_coe, hg, hg', one_mul, mul_one]
  rfl

lemma adZeroRep_inv_eq_one {g : Γ} (hg : ρbar.adZeroRep g = 1) : ρbar.adZeroRep g⁻¹ = 1 := by
  have : ρbar.adZeroRep g⁻¹ * ρbar.adZeroRep g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rwa [hg, mul_one] at this

lemma dualTwist_ρ_apply_of_adZeroRep (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ}
    (hg : ρbar.adZeroRep g = 1) (f : (Rep.of ρ₀).dualTwist (cycloChar p)) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ g f = ((cycloChar p g : (ZMod p)ˣ) : ZMod p) • f := by
  rw [Rep.dualTwist_ρ_apply]
  congr 1
  have h1 : ρ₀ g⁻¹ = 1 := rho0_eq_one_of_adZeroRep hρ₀ (adZeroRep_inv_eq_one hg)
  change f ∘ₗ ρ₀ g⁻¹ = f
  rw [h1]
  rfl

lemma dualTwist_ρ_eq_one (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ}
    (h1 : ρbar.adZeroRep g = 1) (h2 : cycloChar p g = 1) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ g = 1 := by
  apply LinearMap.ext
  intro f
  rw [dualTwist_ρ_apply_of_adZeroRep hρ₀ h1, h2, Units.val_one, one_smul]
  rfl

lemma cycloChar_eq_one_of_apply_eq_self {n : ℕ} {ζ : Qb} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    {g : Γ} (hg : g ζ = ζ) : cycloChar p g = 1 := by
  have hp : p.Prime := Fact.out
  have hζ' : IsPrimitiveRoot (ζ ^ p ^ n) p :=
    hζ.pow (pow_pos hp.pos _) (by rw [pow_succ])
  exact cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p g hζ' (by rw [map_pow, hg])

lemma rho0_apply_coe (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) (g : Γ)
    (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρ₀ g f : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)
      = ρbar.ρ g * f * ρbar.ρ g⁻¹ := by
  rw [hρ₀ g f]
  rfl

end Dual

section Invariants

variable {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]

variable (p) in
lemma invariants_eq_bot (hp2 : p ≠ 2) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ.invariants = ⊥ := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : Module.Finite (ZMod p) k := Module.Finite.of_finite
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_charP k p hp2
  refine Rep.dualTwist_of_invariants_eq_bot_of_forall_linearMap_eq_zero
    (k := ZMod p) (K := k) ρbar.adZeroRep ρ₀ hρ₀ (cycloChar p) ?_
  intro φ hφ
  let χ : Γ →* kˣ := (Units.map (algebraMap (ZMod p) k : ZMod p →* k)).comp (cycloChar p)
  refine ResidualGaloisRep.eq_zero_of_forall_map_adZeroRep_eq_smul h2 ρbar habs hTW χ φ ?_
  intro σ f
  rw [hφ σ f]
  simp [χ]

end Invariants

lemma irreducible_ker_cycloChar {k : Type} [Field k] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    {ξ : Qb} (hξ : IsPrimitiveRoot ξ p)
    (W : Submodule k ρbar.V)
    (hW : ∀ g : Γ, cycloChar p g = 1 → ∀ x ∈ W, ρbar.ρ g x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let e : ρbar.V ≃ₗ[k] (ρbar.baseChange k).V := (TensorProduct.lid k ρbar.V).symm
  let W' : Submodule k (ρbar.baseChange k).V := W.map (e : ρbar.V →ₗ[k] (ρbar.baseChange k).V)
  have hnat : ∀ (σ : Γ) (x : (ρbar.baseChange k).V),
      e.symm ((ρbar.baseChange k).ρ σ x) = ρbar.ρ σ (e.symm x) := by
    intro σ x
    change TensorProduct.lid k ρbar.V ((ρbar.ρ σ).baseChange k x) =
      ρbar.ρ σ (TensorProduct.lid k ρbar.V x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have hW' : ∀ σ : Γ, σ ξ = ξ → ∀ x ∈ W', (ρbar.baseChange k).ρ σ x ∈ W' := by
    intro σ hσ x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    rw [hnat]
    exact hW σ (cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p σ hξ hσ) _ hx
  have hξ1 : IsPrimitiveRoot ξ (p ^ 1) := by rwa [pow_one]
  have hcl := ResidualGaloisRep.baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
    ρbar habs hTW hp2 hξ1 k W' hW'
  have hWW' : W = W'.map (e.symm : (ρbar.baseChange k).V →ₗ[k] ρbar.V) := by
    rw [← Submodule.map_comp]
    simp
  rcases hcl with h | h
  · left; rw [hWW', h, Submodule.map_bot]
  · right; rw [hWW', h, Submodule.map_top, LinearEquiv.range]

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
    {n : ℕ} (hn : 0 < n) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist (cycloChar p)))
    (hc : H1π ((Rep.of ρ₀).dualTwist (cycloChar p)) c ≠ 0) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      τ ζ = ζ ∧ ρbar.adZeroRep τ = 1 ∧ c τ ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  revert c
  set M : Rep (ZMod p) Γ := (Rep.of ρ₀).dualTwist (cycloChar p) with hM
  intro c hc
  by_contra hne
  push Not at hne
  apply hc
  have hNpos : 0 < p ^ (m + 1) := pow_pos hp.pos _

  have hNtriv : ∀ τ : Γ, τ ζ = ζ → ρbar.adZeroRep τ = 1 → M.ρ τ = 1 := fun τ h1 h2 =>
    dualTwist_ρ_eq_one hρ₀ h2 (cycloChar_eq_one_of_apply_eq_self hζ h1)

  have hkey : ∀ g x : Γ, ρbar.adZeroRep x = 1 →
      M.ρ g (c x) - c x = ((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g - c g := by
    intro g x hx

    have hcomm_ζ : (g * x * g⁻¹ * x⁻¹) ζ = ζ := commutator_apply_eq hNpos hζ g x
    have hcomm_ad : ρbar.adZeroRep (g * x * g⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, hx, mul_one, adZeroRep_inv_eq_one hx, mul_one, ← map_mul,
        mul_inv_cancel, map_one]
    have hcN : c (g * x * g⁻¹ * x⁻¹) = 0 := hne _ hcomm_ζ hcomm_ad
    have hcocy := (mem_cocycles₁_iff c).1 c.2

    have hA : c (g * x * g⁻¹) = c x := by
      have h := hcocy (g * x * g⁻¹ * x⁻¹) x
      rw [inv_mul_cancel_right] at h
      rw [h, hcN, add_zero, hNtriv _ hcomm_ζ hcomm_ad, Module.End.one_apply]

    have hB : c (g * x * g⁻¹) = c g + M.ρ g (c x) -
        ((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g := by
      have h1 := hcocy (g * x) g⁻¹
      have h2 := hcocy g x
      have h3 : M.ρ (g * x) (c g⁻¹) = -(((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g) := by
        rw [map_mul, Module.End.mul_apply, dualTwist_ρ_apply_of_adZeroRep hρ₀ hx, map_smul,
          cocycles₁_map_inv, smul_neg]
      rw [h1, h2, h3]
      abel
    rw [hA] at hB
    have := hB

    calc M.ρ g (c x) - c x
        = M.ρ g (c x) - (c g + M.ρ g (c x) - ((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g) := by
          rw [← this]
      _ = ((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g - c g := by abel

  by_cases hA : ∃ x : Γ, ρbar.adZeroRep x = 1 ∧ cycloChar p x ≠ 1
  · obtain ⟨x, hx, hχx⟩ := hA
    set s : ZMod p := ((cycloChar p x : (ZMod p)ˣ) : ZMod p) - 1 with hs
    have hs0 : s ≠ 0 := by
      intro h
      apply hχx
      ext
      rw [Units.val_one]
      exact sub_eq_zero.1 h
    rw [H1π_eq_zero_iff]
    refine ⟨s⁻¹ • c x, ?_⟩
    funext g
    have hsg : ((cycloChar p x : (ZMod p)ˣ) : ZMod p) • c g - c g = s • c g := by
      rw [hs]
      exact ((sub_smul _ (1 : ZMod p) (c g)).trans (by rw [one_smul])).symm
    have e1 : s⁻¹ • M.ρ g (c x) - s⁻¹ • c x = s⁻¹ • (M.ρ g (c x) - c x) := (smul_sub _ _ _).symm
    rw [d₀₁_hom_apply, map_smul]
    change s⁻¹ • M.ρ g (c x) - s⁻¹ • c x = c g
    rw [e1, hkey g x hx, hsg]
    exact inv_smul_smul₀ hs0 (c g)

  push Not at hA
  have hinv := invariants_eq_bot p hp2 ρbar habs hTW ρ₀ hρ₀
  have hcK : ∀ x : Γ, ρbar.adZeroRep x = 1 → c x = 0 := by
    intro x hx
    have hmem : c x ∈ M.ρ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      have h := hkey g x hx
      rw [hA x hx, Units.val_one, one_smul, sub_self, sub_eq_zero] at h
      exact h
    rw [hinv, Submodule.mem_bot] at hmem
    exact hmem

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := hζ.pow hNpos (by rw [pow_succ])
  exact groupCohomology.H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range p hp2
    ρbar.finrank_eq ρbar.ρ (finite_range_rho ρbar) (cycloChar p) (cycloChar_surjective p)
    (fun W hW => irreducible_ker_cycloChar hp2 ρbar habs hTW hξ W hW)
    ρ₀ (rho0_apply_coe hρ₀)
    (fun g hg => hA g (adZeroRep_eq_one_of_rho0 hρ₀ hg))
    c (fun g hg => hcK g (adZeroRep_eq_one_of_rho0 hρ₀ hg))

end P2mInjRes
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero.P2mInjRes"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero.P2mInjRes"

open P2mInjRes in
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
    {n : ℕ} (hn : 0 < n) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist (cycloChar p)))
    (hc : H1π ((Rep.of ρ₀).dualTwist (cycloChar p)) c ≠ 0) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      τ ζ = ζ ∧ ρbar.adZeroRep τ = 1 ∧ c τ ≠ 0 :=
  main p hp2 ρbar habs hsplit hTW ρ₀ hρ₀ hn hζ c hc

end S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
end P2MW
export P2MW.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero (solution)
