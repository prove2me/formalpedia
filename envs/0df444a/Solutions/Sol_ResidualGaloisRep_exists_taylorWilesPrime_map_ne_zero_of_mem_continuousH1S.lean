-- Prove2me | solution 1 for ResidualGaloisRep.exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/453b091c-9634-5770-9bd8-e5a42028cfa7

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
import Theorems.Thm_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
import Theorems.Thm_ResidualGaloisRep_baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
import Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation IntermediateField

noncomputable section

namespace P2mSeeded

abbrev Qb := AlgebraicClosure ℚ
abbrev Γ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

private lemma _root_.P2mSeeded.exists_isPrimitiveRoot (N : ℕ) [NeZero N] : ∃ ζ₀ : Qb, IsPrimitiveRoot ζ₀ N :=
  IsCyclotomicExtension.exists_isPrimitiveRoot (S := ({N} : Set ℕ)) Qb Qb
    (Set.mem_singleton N) (NeZero.ne N)

p2m_export "P2mSeeded" "exists_isPrimitiveRoot"

section LinAlg

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma charpoly_eq_of_finrank_eq_two (hV : Module.finrank k V = 2) (T : Module.End k V) :
    T.charpoly = X ^ 2 - C (LinearMap.trace k V T) * X + C (LinearMap.det T) := by
  let b := Module.finBasisOfFinrankEq k V hV
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace k b T, LinearMap.det_toMatrix b T]

lemma charpoly_eq_mul_iff (hV : Module.finrank k V = 2) (T : Module.End k V) (a b : k) :
    T.charpoly = (X - C a) * (X - C b) ↔
      LinearMap.trace k V T = a + b ∧ LinearMap.det T = a * b := by
  have hexp : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add, map_mul]; ring
  rw [charpoly_eq_of_finrank_eq_two hV, hexp]
  constructor
  · intro h
    have h1 := congrArg (fun q : k[X] => q.coeff 1) h
    have h0 := congrArg (fun q : k[X] => q.coeff 0) h
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h1 h0
    norm_num at h1 h0
    exact ⟨by linear_combination -h1, h0⟩
  · rintro ⟨h1, h0⟩
    rw [h1, h0]

lemma charpoly_smul_of_charpoly_eq (hV : Module.finrank k V = 2) {T : Module.End k V} {a b : k}
    (h : T.charpoly = (X - C a) * (X - C b)) (c : k) :
    (c • T).charpoly = (X - C (c * a)) * (X - C (c * b)) := by
  rw [charpoly_eq_mul_iff hV] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [map_smul, h.1, smul_eq_mul, mul_add]
  · rw [LinearMap.det_smul, h.2, hV]; ring

lemma exists_eq_smul_one_of_forall_commute (h2 : (2 : k) ≠ 0) (hV : Module.finrank k V = 2)
    (T : Module.End k V)
    (hT : ∀ f : Module.End k V, LinearMap.trace k V f = 0 → T * f = f * T) :
    ∃ c : k, T = c • 1 := by
  classical

  have hall : ∀ f : Module.End k V, T * f = f * T := by
    intro f
    have htr : LinearMap.trace k V (f - (LinearMap.trace k V f / 2) • (1 : Module.End k V)) = 0 := by
      rw [map_sub, map_smul, LinearMap.trace_one, hV, smul_eq_mul]
      push_cast
      field_simp
      ring
    have h := hT _ htr
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_left_inj] at h
    exact h
  let b := Module.finBasisOfFinrankEq k V hV
  have hM : ∀ i j : Fin 2, Commute (Matrix.single i j (1 : k)) (LinearMap.toMatrix b b T) := by
    intro i j
    have h := hall (Matrix.toLin b b (Matrix.single i j 1))
    have h' := congrArg (LinearMap.toMatrix b b) h
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin] at h'
    exact h'.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := LinearMap.toMatrix b b T)
    (fun i j _ => hM i j)
  refine ⟨c, ?_⟩
  apply (LinearMap.toMatrix b b).injective
  rw [← hc, LinearEquiv.map_smul, LinearMap.toMatrix_one, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

end LinAlg

section Dual

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] {ρbar : ResidualGaloisRep k}
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
  {ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (LinearMap.ker (LinearMap.trace k ρbar.V))}

lemma two_ne_zero_of_charP (k : Type) [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP k p] : (2 : k) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

lemma rho0_eq_one_of_adZeroRep (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) {g : Γ}
    (hg : ρbar.adZeroRep g = 1) : ρ₀ g = 1 := by
  apply LinearMap.ext
  intro v
  rw [hρ₀ g v, hg]
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

lemma dualTwist_ρ_eq_one {g : Γ} (h1 : ρ₀ g⁻¹ = 1) (h2 : cycloChar p g = 1) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ g = 1 := by
  ext f v
  rw [Rep.dualTwist_ρ_apply]
  simp [h1, h2]

lemma cycloChar_eq_one_of_apply_eq_self {n : ℕ} {ζ : Qb} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    {g : Γ} (hg : g ζ = ζ) : cycloChar p g = 1 := by
  have hp : p.Prime := Fact.out
  have hζ' : IsPrimitiveRoot (ζ ^ p ^ n) p :=
    hζ.pow (pow_pos hp.pos _) (by rw [pow_succ])
  exact cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p g hζ' (by rw [map_pow, hg])

lemma dualTwist_ρ_eq_one_of_mem (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    {n : ℕ} {ζ : Qb} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    {τ : Γ} (hτζ : τ ζ = ζ) (hτ : ρbar.adZeroRep τ = 1) :
    ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ τ = 1 := by
  refine dualTwist_ρ_eq_one (rho0_eq_one_of_adZeroRep hρ₀ ?_) (cycloChar_eq_one_of_apply_eq_self hζ hτζ)
  have : ρbar.adZeroRep τ⁻¹ * ρbar.adZeroRep τ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rwa [hτ, mul_one] at this

lemma exists_level (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s ∈ E.fixingSubgroup, ((Rep.of ρ₀).dualTwist (cycloChar p)).ρ s = 1 := by
  classical
  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI := hLfd
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot p
  have hξint : IsIntegral ℚ ξ := (isIntegral_algebraicClosure_rat).isIntegral ξ
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hξint
  refine ⟨L ⊔ ℚ⟮ξ⟯, finiteDimensional_sup L ℚ⟮ξ⟯, fun s hs => ?_⟩
  have hsL : ∀ x ∈ L, s x = x := fun x hx =>
    (mem_fixingSubgroup_iff (K := L ⊔ ℚ⟮ξ⟯) s).mp hs x (le_sup_left (a := L) hx)
  have hsξ : s ξ = ξ :=
    (mem_fixingSubgroup_iff (K := L ⊔ ℚ⟮ξ⟯) s).mp hs ξ
      (le_sup_right (a := L) (mem_adjoin_simple_self ℚ ξ))
  have hρs' : ρbar.ρ s⁻¹ = 1 := by
    have hρs : ρbar.ρ s = 1 := hL s hsL
    have : ρbar.ρ s⁻¹ * ρbar.ρ s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rwa [hρs, mul_one] at this
  exact dualTwist_ρ_eq_one (rho0_eq_one_of_adZeroRep hρ₀ (adZeroRep_eq_one_of_rho _ hρs'))
    (cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p s hξ hsξ)

lemma exists_rho_eq_smul_one (h2 : (2 : k) ≠ 0) {τ : Γ} (hτ : ρbar.adZeroRep τ = 1) :
    ∃ c : k, c ≠ 0 ∧ ρbar.ρ τ = c • 1 := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_forall_commute h2 ρbar.finrank_eq (ρbar.ρ τ)
    (fun f hf => by
      have h := congrArg (fun x : LinearMap.ker (LinearMap.trace k ρbar.V) => (x : Module.End k ρbar.V))
        (LinearMap.congr_fun hτ ⟨f, LinearMap.mem_ker.2 hf⟩)
      simp only [ResidualGaloisRep.adZeroRep_apply_coe, Module.End.one_apply] at h
      have h' := congrArg (fun x => x * ρbar.ρ τ) h
      beta_reduce at h'
      rwa [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at h')
  refine ⟨c, ?_, hc⟩
  rintro rfl
  have hu : IsUnit (ρbar.ρ τ) := (Group.isUnit τ).map ρbar.ρ
  rw [hc, zero_smul, isUnit_zero_iff] at hu
  have h1 : (1 : Module.End k ρbar.V) = 0 := hu.symm
  haveI : Subsingleton ρbar.V := ⟨fun v w => by
    have hv := LinearMap.congr_fun h1 v
    have hw := LinearMap.congr_fun h1 w
    simp only [Module.End.one_apply, LinearMap.zero_apply] at hv hw
    rw [hv, hw]⟩
  have : Module.finrank k ρbar.V = 0 := Module.finrank_zero_of_subsingleton
  rw [ρbar.finrank_eq] at this
  exact two_ne_zero this

end Dual

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
    (S : Finset Nat.Primes)
    (ψ : H1 ((Rep.of ρ₀).dualTwist (cycloChar p)))
    (hψS : ψ ∈ continuousH1S S ((Rep.of ρ₀).dualTwist (cycloChar p))) (hψ : ψ ≠ 0)
    (n : ℕ) (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom ψ ≠ 0 := by
  classical
  revert ψ
  set M' : Rep (ZMod p) Γ := (Rep.of ρ₀).dualTwist (cycloChar p) with hM'
  intro ψ hψS hψ
  have hp : p.Prime := Fact.out
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_charP k p hp2

  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p ^ (n + 1))

  obtain ⟨c, ⟨F, hF, hcF⟩, hcψ⟩ := (mem_continuousH1S_iff S M' ψ).1 hψS
  have hc0 : H1π M' c ≠ 0 := by
    intro h; apply hψ; rw [← hcψ]; exact h

  obtain ⟨τ₀, hτ₀ζ, hτ₀ad, hcτ₀⟩ :=
    ResidualGaloisRep.exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero p hp2
      ρbar habs hsplit hTW ρ₀ hρ₀ (Nat.succ_pos n) hζ c hc0

  let Γζ : Subgroup Γ := MulAction.stabilizer Γ ζ
  have memΓζ : ∀ σ : Γ, σ ∈ Γζ ↔ σ ζ = ζ := fun σ => MulAction.mem_stabilizer_iff
  let N : Set Γ := {τ | τ ζ = ζ ∧ ρbar.adZeroRep τ = 1}
  have hNtriv : ∀ τ ∈ N, M'.ρ τ = 1 := fun τ hτ => dualTwist_ρ_eq_one_of_mem hρ₀ hζ hτ.1 hτ.2
  have hcN1 : ∀ τ ∈ N, ∀ g : Γ, c (τ * g) = c τ + c g := by
    intro τ hτ g
    rw [(mem_cocycles₁_iff c).1 c.2, hNtriv τ hτ, Module.End.one_apply, add_comm]

  have hNconj : ∀ h : Γ, h ζ = ζ → ∀ τ ∈ N, h⁻¹ * τ * h ∈ N := by
    intro h hh τ hτ
    have hh' : h⁻¹ ζ = ζ := by
      rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
      exact hh.symm
    refine ⟨?_, ?_⟩
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh, hτ.1, hh']
    · rw [map_mul, map_mul, hτ.2, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hcconj : ∀ h : Γ, ∀ τ ∈ N, c (h⁻¹ * τ * h) = M'.ρ h⁻¹ (c τ) := by
    intro h τ hτ
    have h1 := (mem_cocycles₁_iff c).1 c.2 h⁻¹ (τ * h)
    rw [← mul_assoc] at h1
    rw [h1, hcN1 τ hτ h, map_add, add_assoc, ← (mem_cocycles₁_iff c).1 c.2 h⁻¹ h,
      inv_mul_cancel, cocycles₁_map_one, add_zero]

  let U : AddSubgroup (Module.End k ρbar.V) :=
    { carrier := {m | ∃ hm : LinearMap.trace k ρbar.V m = 0, ∀ τ ∈ N,
        (c τ : M') ⟨m, LinearMap.mem_ker.2 hm⟩ = 0}
      zero_mem' := ⟨by simp, fun τ _ => by
        rw [show (⟨0, _⟩ : LinearMap.ker (LinearMap.trace k ρbar.V)) = 0 from rfl, map_zero]⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨by rw [map_add, ha, hb, add_zero], fun τ hτ => ?_⟩
        rw [show (⟨a + b, _⟩ : LinearMap.ker (LinearMap.trace k ρbar.V)) =
          ⟨a, LinearMap.mem_ker.2 ha⟩ + ⟨b, LinearMap.mem_ker.2 hb⟩ from rfl, map_add,
          ha' τ hτ, hb' τ hτ, add_zero]
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨by rw [map_neg, ha, neg_zero], fun τ hτ => ?_⟩
        rw [show (⟨-a, _⟩ : LinearMap.ker (LinearMap.trace k ρbar.V)) =
          -⟨a, LinearMap.mem_ker.2 ha⟩ from rfl, map_neg, ha' τ hτ, neg_zero] }
  have memU : ∀ m : Module.End k ρbar.V, m ∈ U ↔ ∃ hm : LinearMap.trace k ρbar.V m = 0,
      ∀ τ ∈ N, (c τ : M') ⟨m, LinearMap.mem_ker.2 hm⟩ = 0 := fun m => Iff.rfl

  let ρ : Γζ →* Module.End k ρbar.V := ρbar.ρ.comp Γζ.subtype
  have hρ : ∀ h : Γζ, ρ h = ρbar.ρ (h : Γ) := fun h => rfl

  have hU : ∀ h : Γζ, ∀ m ∈ U, ρ h * m * ρ h⁻¹ ∈ U := by
    intro h m hm
    obtain ⟨hm0, hm1⟩ := (memU m).1 hm
    have hhζ : (h : Γ) ζ = ζ := (memΓζ h).1 h.2
    have htr : LinearMap.trace k ρbar.V (ρ h * m * ρ h⁻¹) = 0 := by
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, hm0]
    refine (memU _).2 ⟨htr, fun τ hτ => ?_⟩
    have hτ' := hNconj (h : Γ) hhζ τ hτ
    have h0 := hm1 _ hτ'
    rw [hcconj (h : Γ) τ hτ] at h0

    have h0' : ((cycloChar p (h : Γ)⁻¹ : (ZMod p)ˣ) : ZMod p) •
        (c τ : M') (ρ₀ (h : Γ) ⟨m, LinearMap.mem_ker.2 hm0⟩) = 0 := by
      have := h0
      rw [show M'.ρ (h : Γ)⁻¹ (c τ) = ((cycloChar p (h : Γ)⁻¹ : (ZMod p)ˣ) : ZMod p) •
        ((c τ : M') ∘ₗ ρ₀ ((h : Γ)⁻¹)⁻¹) from rfl, inv_inv] at this
      exact this
    rw [smul_eq_zero] at h0'
    rcases h0' with h0' | h0'
    · exact absurd h0' (Units.ne_zero _)
    · rw [hρ₀] at h0'
      convert h0' using 2
      first | rfl | exact Subtype.ext (by simp [ResidualGaloisRep.adZeroRep_apply_coe]) | exact Subtype.ext (by simp [ResidualGaloisRep.adZeroRep_apply_coe]; rfl)

  have hproper : ∃ m : Module.End k ρbar.V, LinearMap.trace k ρbar.V m = 0 ∧ m ∉ U := by
    by_contra hall
    push Not at hall
    apply hcτ₀
    apply LinearMap.ext
    intro v
    obtain ⟨hv0, hv⟩ := (memU _).1 (hall (v : Module.End k ρbar.V) (LinearMap.mem_ker.1 v.2))
    have := hv τ₀ ⟨hτ₀ζ, hτ₀ad⟩
    rw [LinearMap.zero_apply]
    convert this

  have hirr : ∀ W : Submodule k ρbar.V, (∀ h : Γζ, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
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
    have hW' : ∀ σ : Γ, σ ζ = ζ → ∀ x ∈ W', (ρbar.baseChange k).ρ σ x ∈ W' := by
      intro σ hσ x hx
      rw [Submodule.mem_map_equiv] at hx ⊢
      rw [hnat]
      exact hW ⟨σ, (memΓζ σ).2 hσ⟩ _ hx
    have hcl := ResidualGaloisRep.baseChange_submodule_eq_bot_or_eq_top_of_forall_apply_eq_self
      ρbar habs hTW hp2 hζ k W' hW'
    have hWW' : W = W'.map (e.symm : (ρbar.baseChange k).V →ₗ[k] ρbar.V) := by
      rw [← Submodule.map_comp]
      simp
    rcases hcl with h | h
    · left; rw [hWW', h, Submodule.map_bot]
    · right; rw [hWW', h, Submodule.map_top, LinearEquiv.range]
  have hsplit' : ∀ h : Γζ, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β) :=
    fun h => hsplit (h : Γ)

  obtain ⟨h, α, β, hαβ, hchar, m, hm0, hcomm, hmU⟩ :=
    Module.End.exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible h2
      ρbar.finrank_eq ρ hirr hsplit' U hU hproper
  have hτex : ∃ τ ∈ N, (c τ : M') ⟨m, LinearMap.mem_ker.2 hm0⟩ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hmU ((memU m).2 ⟨hm0, hne⟩)
  obtain ⟨τ, hτN, hτm⟩ := hτex
  set σ₀ : Γ := (h : Γ) with hσ₀
  have hσ₀ζ : σ₀ ζ = ζ := (memΓζ _).1 h.2
  have hchar₀ : LinearMap.charpoly (ρbar.ρ σ₀) = (X - C α) * (X - C β) := hchar
  have hcomm₀ : m * ρbar.ρ σ₀ = ρbar.ρ σ₀ * m := hcomm

  have hnot : c τ ∉ LinearMap.range (M'.ρ σ₀ - 1) := by
    rintro ⟨f, hf⟩
    apply hτm
    rw [← hf, LinearMap.sub_apply, Module.End.one_apply]
    change ((cycloChar p σ₀ : (ZMod p)ˣ) : ZMod p) • ((f : M') ∘ₗ ρ₀ σ₀⁻¹)
      ⟨m, LinearMap.mem_ker.2 hm0⟩ - f ⟨m, LinearMap.mem_ker.2 hm0⟩ = 0
    rw [cycloChar_eq_one_of_apply_eq_self hζ hσ₀ζ, Units.val_one, one_smul, LinearMap.comp_apply,
      sub_eq_zero]
    congr 1
    rw [hρ₀]
    apply Subtype.ext
    rw [ResidualGaloisRep.adZeroRep_apply_coe, inv_inv]
    change ρbar.ρ σ₀⁻¹ * m * ρbar.ρ σ₀ = m
    rw [mul_assoc, hcomm₀, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

  have hseed : ∃ σ : Γ, σ ζ = ζ ∧ (∃ α β : k, α ≠ β ∧
      LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β)) ∧
        c σ ∉ LinearMap.range (M'.ρ σ - 1) := by
    by_cases hs : c σ₀ ∈ LinearMap.range (M'.ρ σ₀ - 1)
    · refine ⟨τ * σ₀, ?_, ?_, ?_⟩
      · rw [AlgEquiv.mul_apply, hσ₀ζ, hτN.1]
      · obtain ⟨d, hd0, hd⟩ := exists_rho_eq_smul_one h2 hτN.2
        refine ⟨d * α, d * β, fun h => hαβ (mul_left_cancel₀ hd0 h), ?_⟩
        rw [map_mul, hd, smul_mul_assoc, one_mul]
        exact charpoly_smul_of_charpoly_eq ρbar.finrank_eq hchar₀ d
      · have hρτσ : M'.ρ (τ * σ₀) = M'.ρ σ₀ := by rw [map_mul, hNtriv τ hτN, one_mul]
        rw [hρτσ, hcN1 τ hτN σ₀]
        intro hmem
        exact hnot (by simpa using Submodule.sub_mem _ hmem hs)
    · exact ⟨σ₀, hσ₀ζ, ⟨α, β, hαβ, hchar₀⟩, hs⟩
  obtain ⟨σ, hσζ, ⟨α', β', hαβ', hcharσ⟩, hcσ⟩ := hseed

  obtain ⟨q, hqT, hmod, hunr, hfrob, hres⟩ :=
    ResidualGaloisRep.exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range ρbar hζ M'
      (exists_level hρ₀) c ⟨F, hF.1, hcF⟩ hσζ hαβ' hcharσ hcσ T
  refine ⟨q, hqT, hmod.of_dvd (pow_dvd_pow p (Nat.le_succ n)), hunr, hfrob, ?_⟩
  rw [← hcψ]
  exact hres

end P2mSeeded
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S.P2mSeeded"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S.P2mSeeded"

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
    (S : Finset Nat.Primes)
    (ψ : H1 ((Rep.of ρ₀).dualTwist (cycloChar p)))
    (hψS : ψ ∈ continuousH1S S ((Rep.of ρ₀).dualTwist (cycloChar p))) (hψ : ψ ≠ 0)
    (n : ℕ) (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom ψ ≠ 0 :=
  P2mSeeded.main p hp2 ρbar habs hsplit hTW ρ₀ hρ₀ S ψ hψS hψ n T

end S_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S
end P2MW
export P2MW.S_ResidualGaloisRep_exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S (solution)
