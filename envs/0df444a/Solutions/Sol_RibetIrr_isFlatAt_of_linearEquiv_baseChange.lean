-- Prove2me | solution 1 for RibetIrr.isFlatAt_of_linearEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d2d55a28-99be-5bc5-bcc3-f255fdd5a5c8

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_isFlatAt_of_linearEquiv_baseChange

set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct Pointwise

set_option autoImplicit false

noncomputable section

namespace Sol7Lat

theorem ne_bot_of_finite_quotient {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (I : Ideal R) (hI : Finite (R ⧸ I)) : I ≠ ⊥ := by
  rintro rfl
  have : Finite R := Finite.of_equiv _ ((Submodule.quotEquivOfEqBot (⊥ : Ideal R) rfl).toEquiv)
  exact IsDiscreteValuationRing.not_isField R (Finite.isField_of_domain R)

private def gHat {R : Type} [CommRing R] (ϖ : R) (n : ℕ) :
    (R ⧸ (Ideal.span {ϖ} : Ideal R)) →ₗ[R] R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R) :=
  Submodule.mapQ _ _ (LinearMap.lsmul R R (ϖ ^ n)) (by
    intro x hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [← hc]; ring⟩)

private theorem gHat_mk {R : Type} [CommRing R] (ϖ : R) (n : ℕ) (c : R) :
    gHat ϖ n (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (ϖ ^ n * c) := rfl

theorem finite_quotient_span_pow {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [hres : Finite (IsLocalRing.ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) : ∀ n : ℕ, Finite (R ⧸ (Ideal.span {ϖ ^ n} : Ideal R)) := by
  have hres1 : Finite (R ⧸ (Ideal.span {ϖ} : Ideal R)) :=
    Finite.of_equiv (IsLocalRing.ResidueField R)
      (Submodule.quotEquivOfEq _ _ hϖ.maximalIdeal_eq).toEquiv
  intro n
  induction n with
  | zero =>
    have : Subsingleton (R ⧸ (Ideal.span {ϖ ^ 0} : Ideal R)) := by
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
    exact Finite.of_subsingleton
  | succ n ih =>
    have hle : (Ideal.span {ϖ ^ (n + 1)} : Ideal R) ≤ Ideal.span {ϖ ^ n} :=
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n))
    set q : R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R) →+*
        R ⧸ (Ideal.span {ϖ ^ n} : Ideal R) := Ideal.Quotient.factor hle with hqdef

    have hker : {y : R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R) | q y = 0} =
        Set.range (gHat ϖ n) := by
      ext y
      constructor
      · intro hy
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hr : r ∈ (Ideal.span {ϖ ^ n} : Ideal R) := by
          have : q (Ideal.Quotient.mk _ r) = 0 := hy
          rwa [hqdef, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at this
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
        exact ⟨Ideal.Quotient.mk _ c, by rw [gHat_mk]; congr 1; rw [← hc]; ring⟩
      · rintro ⟨cbar, rfl⟩
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cbar
        show q (gHat ϖ n (Ideal.Quotient.mk _ c)) = 0
        rw [gHat_mk, hqdef, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self _)

    have hfin0 : ({y | q y = 0} : Set (R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R))).Finite := by
      rw [hker]; exact Set.finite_range _
    have hfib : ∀ b : R ⧸ (Ideal.span {ϖ ^ n} : Ideal R), (q ⁻¹' {b}).Finite := by
      intro b
      rcases (q ⁻¹' {b}).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
      · rw [he]; exact Set.finite_empty
      · have : q ⁻¹' {b} ⊆ (fun y => x₀ + y) '' {y | q y = 0} := by
          intro x hx
          refine ⟨x - x₀, ?_, by ring⟩
          have hqx : q x = b := hx
          have hqx₀ : q x₀ = b := hx₀
          simp only [Set.mem_setOf_eq, map_sub, hqx, hqx₀, sub_self]
        exact Set.Finite.subset (hfin0.image _) this
    have : (Set.univ : Set (R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R))).Finite := by
      have hcov : (Set.univ : Set (R ⧸ (Ideal.span {ϖ ^ (n + 1)} : Ideal R))) =
          ⋃ b : R ⧸ (Ideal.span {ϖ ^ n} : Ideal R), q ⁻¹' {b} := by
        ext x; simp
      rw [hcov]
      exact Set.finite_iUnion hfib
    exact Set.finite_univ_iff.mp this

theorem finite_quotient_of_ne_bot {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  rw [hn]
  exact finite_quotient_span_pow hϖ n

theorem injective_mapQ_comap {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (L W : Submodule A M) :
    Function.Injective (Submodule.mapQ (W.comap L.subtype) W L.subtype
      (fun _ hx => hx)) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply] at hab
  rw [Submodule.Quotient.eq] at hab ⊢
  exact hab

theorem mem_smul_top_of_exists {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (c : A) (L : Submodule A M) (x : ↥L)
    (hx : ∃ v ∈ L, (x : M) = c • v) :
    x ∈ (Ideal.span {c} : Ideal A) • (⊤ : Submodule A ↥L) := by
  obtain ⟨v, hvL, hv⟩ := hx
  have hxv : x = c • (⟨v, hvL⟩ : ↥L) := Subtype.ext (by simpa using hv)
  rw [hxv]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) trivial

theorem comap_smul_top_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (ϖ : A) (j k : ℕ) (L : Submodule A M)
    (hj : (Ideal.span {ϖ ^ j} : Ideal A) • (⊤ : Submodule A M) ≤ L) :
    ((Ideal.span {ϖ ^ (k + j)} : Ideal A) • (⊤ : Submodule A M)).comap L.subtype ≤
      (Ideal.span {ϖ ^ k} : Ideal A) • (⊤ : Submodule A ↥L) := by
  intro x hx
  have hxM : (x : M) ∈ (Ideal.span {ϖ ^ (k + j)} : Ideal A) • (⊤ : Submodule A M) := hx
  rw [Submodule.ideal_span_singleton_smul] at hxM
  obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hxM
  have hvL : ϖ ^ j • v ∈ L := hj <| by
    rw [Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul v _ _ trivial
  exact mem_smul_top_of_exists (ϖ ^ k) L x
    ⟨ϖ ^ j • v, hvL, by rw [← hv, pow_add, mul_smul]⟩

end Sol7Lat

end

namespace RibetFlatW01

theorem w01b_tmul_one_injective
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] (K : Type) [Field K] [Algebra 𝒪' K]
    [IsFractionRing 𝒪' K]
    (V : Type) [AddCommGroup V] [Module 𝒪' V] [Module.Free 𝒪' V] :
    Function.Injective (fun v : V => (1 : K) ⊗ₜ[𝒪'] v) := by
  intro v w h
  let b := Module.Free.chooseBasis 𝒪' V
  apply b.repr.injective
  ext i
  apply IsFractionRing.injective 𝒪' K
  have h' := congrArg (fun x => (b.baseChange K).repr x i) h
  simp only [Module.Basis.baseChange_repr_tmul] at h'
  rwa [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h'

theorem w01b_exists_integral_multiple
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] (K : Type) [Field K] [Algebra 𝒪' K]
    [IsFractionRing 𝒪' K]
    (V₁ V₂ : Type) [AddCommGroup V₁] [Module 𝒪' V₁] [Module.Free 𝒪' V₁] [Module.Finite 𝒪' V₁]
    [AddCommGroup V₂] [Module 𝒪' V₂] [Module.Free 𝒪' V₂] [Module.Finite 𝒪' V₂]
    (f : K ⊗[𝒪'] V₁ →ₗ[K] K ⊗[𝒪'] V₂) :
    ∃ (d : 𝒪') (φ : V₁ →ₗ[𝒪'] V₂), d ≠ 0 ∧
      ∀ v : V₁, (1 : K) ⊗ₜ[𝒪'] φ v = d • f ((1 : K) ⊗ₜ[𝒪'] v) := by
  classical
  let b₁ := Module.Free.chooseBasis 𝒪' V₁
  let b₂ := Module.Free.chooseBasis 𝒪' V₂
  obtain ⟨d, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪')
    (fun ik : Module.Free.ChooseBasisIndex 𝒪' V₁ × Module.Free.ChooseBasisIndex 𝒪' V₂ =>
      (b₂.baseChange K).repr (f ((1 : K) ⊗ₜ[𝒪'] b₁ ik.1)) ik.2)
  choose a ha using fun ik => RingHom.mem_rangeS.mp (hint ik)
  have ha' : ∀ i k, algebraMap 𝒪' K (a (i, k)) =
      (d : 𝒪') • (b₂.baseChange K).repr (f ((1 : K) ⊗ₜ[𝒪'] b₁ i)) k := fun i k => ha (i, k)
  refine ⟨d, b₁.constr 𝒪' (fun i => ∑ k, a (i, k) • b₂ k), nonZeroDivisors.coe_ne_zero d, ?_⟩
  intro v
  suffices h : (TensorProduct.mk 𝒪' K V₂ 1).comp (b₁.constr 𝒪' (fun i => ∑ k, a (i, k) • b₂ k))
      = ((d : 𝒪') • (f.restrictScalars 𝒪')).comp (TensorProduct.mk 𝒪' K V₁ 1) by
    have hv := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply] at hv
    exact hv
  refine b₁.ext fun i => ?_
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, Module.Basis.constr_basis,
    LinearMap.smul_apply, LinearMap.restrictScalars_apply]
  rw [TensorProduct.tmul_sum]
  conv_rhs => rw [← (b₂.baseChange K).sum_repr (f ((1 : K) ⊗ₜ[𝒪'] b₁ i)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.tmul_smul, Module.Basis.baseChange_apply, ← smul_assoc, ← ha' i k,
    algebraMap_smul]

theorem w01b_exists_embedding
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ₁ ρ₂ : GaloisRepAdic 𝒪')
    (e : (K ⊗[𝒪'] ρ₁.V) ≃ₗ[K] (K ⊗[𝒪'] ρ₂.V))
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : K ⊗[𝒪'] ρ₁.V),
      e ((ρ₁.ρ σ).baseChange K v) = (ρ₂.ρ σ).baseChange K (e v)) :
    ∃ φ : ρ₁.V →ₗ[𝒪'] ρ₂.V, Function.Injective φ ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ₁.V),
        φ (ρ₁.ρ σ v) = ρ₂.ρ σ (φ v)) ∧
      ∃ t : 𝒪', t ≠ 0 ∧ ∀ w : ρ₂.V, ∃ v : ρ₁.V, φ v = t • w := by
  obtain ⟨d, φ, hd, hφ⟩ := w01b_exists_integral_multiple 𝒪' K ρ₁.V ρ₂.V e.toLinearMap
  obtain ⟨d', ψ, hd', hψ⟩ := w01b_exists_integral_multiple 𝒪' K ρ₂.V ρ₁.V e.symm.toLinearMap
  have hφ' : ∀ v : ρ₁.V, (1 : K) ⊗ₜ[𝒪'] φ v = d • e ((1 : K) ⊗ₜ[𝒪'] v) := fun v => hφ v
  have hψ' : ∀ w : ρ₂.V, (1 : K) ⊗ₜ[𝒪'] ψ w = d' • e.symm ((1 : K) ⊗ₜ[𝒪'] w) := fun w => hψ w
  have hj₁ := w01b_tmul_one_injective 𝒪' K ρ₁.V
  have hj₂ := w01b_tmul_one_injective 𝒪' K ρ₂.V
  have hd0 : algebraMap 𝒪' K d ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective 𝒪' K (by rw [h0, map_zero]))
  refine ⟨φ, ?_, ?_, d * d', mul_ne_zero hd hd', ?_⟩
  ·
    intro v w hvw
    apply hj₁
    have h : (1 : K) ⊗ₜ[𝒪'] φ v = (1 : K) ⊗ₜ[𝒪'] φ w := by rw [hvw]
    rw [hφ', hφ', ← algebraMap_smul K d, ← algebraMap_smul K d, smul_right_inj hd0] at h
    exact e.injective h
  ·
    intro σ v
    apply hj₂
    show (1 : K) ⊗ₜ[𝒪'] φ ((ρ₁.ρ σ) v) = (1 : K) ⊗ₜ[𝒪'] (ρ₂.ρ σ) (φ v)
    calc (1 : K) ⊗ₜ[𝒪'] φ ((ρ₁.ρ σ) v)
          = d • e ((ρ₁.ρ σ).baseChange K ((1 : K) ⊗ₜ[𝒪'] v)) := by
            rw [hφ', LinearMap.baseChange_tmul]
      _ = d • (ρ₂.ρ σ).baseChange K (e ((1 : K) ⊗ₜ[𝒪'] v)) := by rw [he]
      _ = (ρ₂.ρ σ).baseChange K (d • e ((1 : K) ⊗ₜ[𝒪'] v)) := by
            rw [LinearMap.map_smul_of_tower]
      _ = (ρ₂.ρ σ).baseChange K ((1 : K) ⊗ₜ[𝒪'] φ v) := by rw [hφ']
      _ = (1 : K) ⊗ₜ[𝒪'] (ρ₂.ρ σ) (φ v) := LinearMap.baseChange_tmul _ _ _
  ·
    intro w
    refine ⟨ψ w, hj₂ ?_⟩
    show (1 : K) ⊗ₜ[𝒪'] φ (ψ w) = (1 : K) ⊗ₜ[𝒪'] ((d * d') • w)
    calc (1 : K) ⊗ₜ[𝒪'] φ (ψ w) = d • e ((1 : K) ⊗ₜ[𝒪'] ψ w) := hφ' _
      _ = d • e (d' • e.symm ((1 : K) ⊗ₜ[𝒪'] w)) := by rw [hψ']
      _ = d • d' • e (e.symm ((1 : K) ⊗ₜ[𝒪'] w)) := by
            rw [← algebraMap_smul K d', map_smul, algebraMap_smul]
      _ = (d * d') • ((1 : K) ⊗ₜ[𝒪'] w) := by rw [e.apply_symm_apply, smul_smul]
      _ = (1 : K) ⊗ₜ[𝒪'] ((d * d') • w) := (TensorProduct.tmul_smul _ _ _).symm

theorem w01b_exists_embedding_pow
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ₁ ρ₂ : GaloisRepAdic 𝒪')
    (e : (K ⊗[𝒪'] ρ₁.V) ≃ₗ[K] (K ⊗[𝒪'] ρ₂.V))
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : K ⊗[𝒪'] ρ₁.V),
      e ((ρ₁.ρ σ).baseChange K v) = (ρ₂.ρ σ).baseChange K (e v))
    {ϖ : 𝒪'} (hϖ : Irreducible ϖ) :
    ∃ φ : ρ₁.V →ₗ[𝒪'] ρ₂.V, Function.Injective φ ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ₁.V),
        φ (ρ₁.ρ σ v) = ρ₂.ρ σ (φ v)) ∧
      ∃ m : ℕ, ∀ w : ρ₂.V, ∃ v : ρ₁.V, φ v = ϖ ^ m • w := by
  obtain ⟨φ, hinj, heq, t, ht, hcof⟩ := w01b_exists_embedding K ρ₁ ρ₂ e he
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht hϖ
  refine ⟨φ, hinj, heq, m, fun w => ?_⟩
  obtain ⟨v, hv⟩ := hcof ((u : 𝒪') • w)
  exact ⟨v, by rw [hv, smul_smul, hu]⟩

theorem w01b_comap_pow_smul_top_le
    {𝒪' : Type} [CommRing 𝒪'] {V₁ V₂ : Type} [AddCommGroup V₁] [Module 𝒪' V₁]
    [AddCommGroup V₂] [Module 𝒪' V₂]
    (φ : V₁ →ₗ[𝒪'] V₂) (hinj : Function.Injective φ) (ϖ : 𝒪') (m k : ℕ)
    (hcof : ∀ w : V₂, ∃ v : V₁, φ v = ϖ ^ m • w) :
    (Ideal.span {ϖ ^ (k + m)} • (⊤ : Submodule 𝒪' V₂)).comap φ ≤
      Ideal.span {ϖ ^ k} • (⊤ : Submodule 𝒪' V₁) := by
  intro v hv
  rw [Submodule.mem_comap, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨w, -, hw⟩ := hv
  obtain ⟨v', hv'⟩ := hcof w
  have hvv' : v = ϖ ^ k • v' :=
    hinj (by rw [← hw, pow_add, mul_smul, ← hv', map_smul])
  rw [hvv', Submodule.ideal_span_singleton_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem w01b_smul_top_le_comap
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    I • (⊤ : Submodule A ρ.V) ≤ (I • (⊤ : Submodule A ρ.V)).comap (ρ.ρ σ) := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

theorem w01b_comap_smul_top_le_comap
    {A : Type} [CommRing A] [IsLocalRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (φ : ρ₁.V →ₗ[A] ρ₂.V)
    (heq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ₁.V),
      φ (ρ₁.ρ σ v) = ρ₂.ρ σ (φ v))
    (J : Ideal A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (J • (⊤ : Submodule A ρ₂.V)).comap φ ≤
      ((J • (⊤ : Submodule A ρ₂.V)).comap φ).comap (ρ₁.ρ σ) := by
  intro v hv
  rw [Submodule.mem_comap] at hv
  rw [Submodule.mem_comap, Submodule.mem_comap, heq]
  exact w01b_smul_top_le_comap ρ₂ J σ hv

theorem w01b_mapQ_comap_injective
    {A : Type} [CommRing A] {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] (φ : V₁ →ₗ[A] V₂) (Q : Submodule A V₂) :
    Function.Injective (Submodule.mapQ (Q.comap φ) Q φ le_rfl) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr hx

theorem w01b_mapQ_comap_equivariant
    {A : Type} [CommRing A] [IsLocalRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (φ : ρ₁.V →ₗ[A] ρ₂.V)
    (heq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ₁.V),
      φ (ρ₁.ρ σ v) = ρ₂.ρ σ (φ v))
    (J : Ideal A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : ρ₁.V ⧸ (J • (⊤ : Submodule A ρ₂.V)).comap φ) :
    Submodule.mapQ ((J • (⊤ : Submodule A ρ₂.V)).comap φ) (J • ⊤) φ le_rfl
        (Submodule.mapQ _ _ (ρ₁.ρ σ) (w01b_comap_smul_top_le_comap ρ₁ ρ₂ φ heq J σ) x) =
      ρ₂.levelAction J σ
        (Submodule.mapQ ((J • (⊤ : Submodule A ρ₂.V)).comap φ) (J • ⊤) φ le_rfl x) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [GaloisRepAdic.levelAction, Submodule.mapQ_apply, heq]

theorem w01b_factor_surjective
    {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    {W W' : Submodule A V} (h : W ≤ W') :
    Function.Surjective (Submodule.factor h) := by
  intro y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk v, Submodule.factor_mk h v⟩

theorem w01b_factor_equivariant
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (W : Submodule A ρ.V)
    (hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, W ≤ W.comap (ρ.ρ σ))
    (I : Ideal A) (h : W ≤ I • (⊤ : Submodule A ρ.V))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ.V ⧸ W) :
    Submodule.factor h (Submodule.mapQ W W (ρ.ρ σ) (hW σ) x) =
      ρ.levelAction I σ (Submodule.factor h x) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [GaloisRepAdic.levelAction, Submodule.mapQ_apply]
  rfl

section GenericDMA
variable {G : Type*} [Monoid G] {A : Type*} [CommRing A]
variable {V : Type*} [AddCommGroup V] [Module A V]

@[reducible] noncomputable def stableQuotDMA (ρ : G →* Module.End A V) (W : Submodule A V)
    (hW : ∀ σ, W ≤ Submodule.comap (ρ σ) W) :
    DistribMulAction G (V ⧸ W) where
  smul σ x := Submodule.mapQ W W (ρ σ) (hW σ) x
  one_smul x := by
    refine Submodule.Quotient.induction_on W x fun z => ?_
    change Submodule.mapQ W W (ρ 1) (hW 1) (Submodule.Quotient.mk z) = _
    simp only [Submodule.mapQ_apply, map_one, Module.End.one_apply]
  mul_smul σ τ x := by
    refine Submodule.Quotient.induction_on W x fun z => ?_
    change Submodule.mapQ W W (ρ (σ * τ)) (hW _) (Submodule.Quotient.mk z) =
      Submodule.mapQ W W (ρ σ) (hW σ)
        (Submodule.mapQ W W (ρ τ) (hW τ) (Submodule.Quotient.mk z))
    simp only [Submodule.mapQ_apply, map_mul, Module.End.mul_apply]
  smul_zero σ := map_zero _
  smul_add σ x y := map_add _ x y

end GenericDMA

section LevelActionBridge
variable {A : Type} [CommRing A] [IsLocalRing A]

lemma w01c_Ismul_stable (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (I • (⊤ : Submodule A ρ.V)) ≤ Submodule.comap (ρ.ρ σ) (I • (⊤ : Submodule A ρ.V)) := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

lemma w01c_smul_eq_levelAction (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :
    letI := stableQuotDMA ρ.ρ (I • ⊤) (w01c_Ismul_stable ρ I)
    σ • x = ρ.levelAction I σ x := rfl

end LevelActionBridge

section ClosureStep
variable {A : Type} [CommRing A] [IsLocalRing A]

lemma w01c_model_at_level (p : ℕ) (ρ₁ ρ₂ : GaloisRepAdic A)
    (hlev₂ : ∀ I : Ideal A, Finite (A ⧸ I) →
      ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
        Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
        Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (ρ₂.V ⧸ (I • (⊤ : Submodule A ρ₂.V))),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g),
            (∀ h : H, g h = σ (f h)) → e g = ρ₂.levelAction I σ (e f))
    (I J : Ideal A) (hJ : Finite (A ⧸ J))
    (W : Submodule A ρ₁.V) (hW : ∀ σ, W ≤ Submodule.comap (ρ₁.ρ σ) W)
    (ι : (ρ₁.V ⧸ W) →ₗ[A] (ρ₂.V ⧸ (J • (⊤ : Submodule A ρ₂.V)))) (hι : Function.Injective ι)
    (hι_eq : ∀ σ x,
      ι (Submodule.mapQ W W (ρ₁.ρ σ) (hW σ) x) = ρ₂.levelAction J σ (ι x))
    (q : (ρ₁.V ⧸ W) →ₗ[A] (ρ₁.V ⧸ (I • (⊤ : Submodule A ρ₁.V)))) (hq : Function.Surjective q)
    (hq_eq : ∀ σ x,
      q (Submodule.mapQ W W (ρ₁.ρ σ) (hW σ) x) = ρ₁.levelAction I σ (q x)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ₁.V ⧸ (I • (⊤ : Submodule A ρ₁.V))),
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
          (∀ x : H, g x = σ (f x)) → e' g = ρ₁.levelAction I σ (e' f) := by

  letI := stableQuotDMA ρ₂.ρ (J • ⊤) (w01c_Ismul_stable ρ₂ J)
  letI := stableQuotDMA ρ₁.ρ W hW
  letI := stableQuotDMA ρ₁.ρ (I • ⊤) (w01c_Ismul_stable ρ₁ I)

  obtain ⟨G, cr, hop, hGfin, hGflat, hGcocomm, eG, heG_add, heG_act⟩ := hlev₂ J hJ

  haveI := hGfin; haveI := hGflat; haveI := hGcocomm

  obtain ⟨Hm, crm, hopm, hHmfin, hHmflat, hHmcocomm, eHm, heHm_add, heHm_act⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p G eG heG_add
      (fun σ f g hfg => heG_act σ f g hfg)
      ι.toAddMonoidHom hι (fun σ n => hι_eq σ n)

  haveI := hHmfin; haveI := hHmflat; haveI := hHmcocomm
  obtain ⟨H, crH, hopH, hHfin, hHflat, hHcocomm, eH, heH_add, heH_act⟩ :=
    GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection p Hm eHm heHm_add
      heHm_act q.toAddMonoidHom hq (fun σ n => hq_eq σ n)

  exact ⟨H, crH, hopH, hHfin, hHflat, hHcocomm, eH, heH_add,
    fun σ f g hfg => heH_act σ f g hfg⟩

end ClosureStep

section Wrapper

theorem w01c_level_model {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪']
    [IsDiscreteValuationRing 𝒪'] (ρ₁ ρ₂ : GaloisRepAdic 𝒪') (p : ℕ)
    (φ : ρ₁.V →ₗ[𝒪'] ρ₂.V) (hφinj : Function.Injective φ)
    (hφeq : ∀ σ v, φ (ρ₁.ρ σ v) = ρ₂.ρ σ (φ v))
    {ϖ : 𝒪'} (hϖ : Irreducible ϖ) (m k : ℕ)
    (hφcof : ∀ w : ρ₂.V, ∃ v : ρ₁.V, φ v = ϖ ^ m • w)
    (hlev₂ : ∀ I : Ideal 𝒪', Finite (𝒪' ⧸ I) →
      ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
        Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
        Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
            (ρ₂.V ⧸ (I • (⊤ : Submodule 𝒪' ρ₂.V))),
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g),
            (∀ h : H, g h = σ (f h)) → e g = ρ₂.levelAction I σ (e f))
    (hJfin : Finite (𝒪' ⧸ (Ideal.span {ϖ ^ (k + m)} : Ideal 𝒪'))) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ₁.V ⧸ ((Ideal.span {ϖ ^ k} : Ideal 𝒪') • (⊤ : Submodule 𝒪' ρ₁.V))),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g),
          (∀ h : H, g h = σ (f h)) →
            e g = ρ₁.levelAction (Ideal.span {ϖ ^ k}) σ (e f) := by
  have _ := hϖ
  let J : Ideal 𝒪' := Ideal.span {ϖ ^ (k + m)}
  let W : Submodule 𝒪' ρ₁.V := (J • (⊤ : Submodule 𝒪' ρ₂.V)).comap φ
  have hW : ∀ σ, W ≤ Submodule.comap (ρ₁.ρ σ) W :=
    w01b_comap_smul_top_le_comap ρ₁ ρ₂ φ hφeq J
  have hWI : W ≤ Ideal.span {ϖ ^ k} • (⊤ : Submodule 𝒪' ρ₁.V) :=
    w01b_comap_pow_smul_top_le φ hφinj ϖ m k hφcof
  exact w01c_model_at_level p ρ₁ ρ₂ hlev₂ (Ideal.span {ϖ ^ k}) J hJfin W hW
    (Submodule.mapQ W (J • ⊤) φ le_rfl)
    (w01b_mapQ_comap_injective φ (J • ⊤))
    (w01b_mapQ_comap_equivariant ρ₁ ρ₂ φ hφeq J)
    (Submodule.factor hWI)
    (Submodule.factor_surjective hWI)
    (w01b_factor_equivariant ρ₁ W hW (Ideal.span {ϖ ^ k}) hWI)

end Wrapper

end RibetFlatW01

open RibetFlatW01 in
theorem solution
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ₁ ρ₂ : GaloisRepAdic 𝒪') (p : ℕ)
    (e : (K ⊗[𝒪'] ρ₁.V) ≃ₗ[K] (K ⊗[𝒪'] ρ₂.V))
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : K ⊗[𝒪'] ρ₁.V),
      e ((ρ₁.ρ σ).baseChange K v) = (ρ₂.ρ σ).baseChange K (e v))
    (hflat₂ : ρ₂.IsFlatAt p) :
    ρ₁.IsFlatAt p := by
  obtain ⟨hres, hlev₂⟩ := hflat₂
  refine ⟨hres, fun I hI => ?_⟩
  haveI : Finite (IsLocalRing.ResidueField 𝒪') := hres
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪'
  obtain ⟨k, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (Sol7Lat.ne_bot_of_finite_quotient _ hI) hϖ
  obtain ⟨φ, hφinj, hφeq, m, hφcof⟩ := w01b_exists_embedding_pow K ρ₁ ρ₂ e he hϖ
  have hJfin : Finite (𝒪' ⧸ (Ideal.span {ϖ ^ (k + m)} : Ideal 𝒪')) :=
    Sol7Lat.finite_quotient_span_pow hϖ (k + m)
  exact w01c_level_model ρ₁ ρ₂ p φ hφinj hφeq hϖ m k hφcof hlev₂ hJfin

end S_RibetIrr_isFlatAt_of_linearEquiv_baseChange
end P2MW
export P2MW.S_RibetIrr_isFlatAt_of_linearEquiv_baseChange (solution)
