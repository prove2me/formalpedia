-- Prove2me | solution 1 for ValuationSubring.exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4e75779e-d5f5-5cae-8307-6e02c580e056

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 32000000

open scoped TensorProduct

theorem solution
    (A : Type) [CommRing A] [IsLocalRing A]
    (k : Type) [Field k] [Algebra A k] (hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0)
    [Algebra (IsLocalRing.ResidueField A) k]
    (hκk : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a) = algebraMap A k a)
    {K : Type} [Field K] [Algebra A K]
    (V : ValuationSubring K) (hVA : ∀ a : A, algebraMap A K a ∈ V)
    [Algebra A ↥V] (halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : K) = algebraMap A K a)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hunif : ∀ f : K, f ∈ V.nonunits → ∃ g : K, g ∈ V ∧ f = algebraMap A K ϖ * g)
    (E : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)))
    (θ : IsLocalRing.ResidueField ↥V ≃+* ↥E)
    (hθ : ∀ a : A, θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥E (IsLocalRing.residue A a))
    (hLD : ∀ (n : ℕ) (f : Fin n → LaurentSeries (IsLocalRing.ResidueField A)),
      LinearIndependent (IsLocalRing.ResidueField A) f →
      LinearIndependent k (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) ∘ f))
    (E' : IntermediateField k (LaurentSeries k))
    (hE' : IntermediateField.adjoin k
      (⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) '' ((E : Set (LaurentSeries (IsLocalRing.ResidueField A))))) = E')
    (𝔮 : Ideal (k ⊗[A] ↥V)) (h𝔮 : 𝔮 ∈ minimalPrimes (k ⊗[A] ↥V)) :
    ∃ Φ : FractionRing ((k ⊗[A] ↥V) ⧸ 𝔮) ≃ₐ[k] ↥E',
      ∀ v : ↥V,
        (((Φ (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) 1)) : ↥E') : LaurentSeries k)
          = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
              ((θ (IsLocalRing.residue ↥V v) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := by
  classical

  subst hE'
  set S : Set (LaurentSeries k) :=
    ⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)) '' ((E : Set (LaurentSeries (IsLocalRing.ResidueField A)))) with hSdef
  set E' : IntermediateField k (LaurentSeries k) := IntermediateField.adjoin k S with hE'def

  have hϖ0 : algebraMap A k ϖ = 0 := hk ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  have htmul_nonunit : ∀ v : ↥V, (v : K) ∈ V.nonunits → (1 : k) ⊗ₜ[A] v = 0 := by
    intro v hv
    obtain ⟨g, hg, hvg⟩ := hunif v hv
    have hv' : v = algebraMap A ↥V ϖ * ⟨g, hg⟩ := Subtype.ext (by rw [Subring.coe_mul, halgV]; exact hvg)
    rw [hv', Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul, Algebra.smul_def,
      hϖ0, zero_mul, TensorProduct.zero_tmul]
  have htmul_maximal : ∀ v : ↥V, v ∈ IsLocalRing.maximalIdeal ↥V → (1 : k) ⊗ₜ[A] v = 0 := fun v hv =>
    htmul_nonunit v (ValuationSubring.coe_mem_nonunits_iff.mpr hv)

  let ψL : ↥V →+* LaurentSeries k :=
    (ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)).comp ((algebraMap ↥E (LaurentSeries (IsLocalRing.ResidueField A))).comp
      ((θ : IsLocalRing.ResidueField ↥V →+* ↥E).comp (IsLocalRing.residue ↥V)))
  have hψL_mem : ∀ v : ↥V, ψL v ∈ E' := fun v =>
    IntermediateField.subset_adjoin k S ⟨_, (θ (IsLocalRing.residue ↥V v)).2, rfl⟩
  let ψ₀ : ↥V →+* ↥E' := ψL.codRestrict E' hψL_mem
  letI algAF : Algebra A ↥E' := ((algebraMap k ↥E').comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k ↥E' := IsScalarTower.of_algebraMap_eq (fun a => rfl)

  have hC : ∀ (F : Type) [Field F] (x : F), algebraMap F (LaurentSeries F) x = HahnSeries.C x := fun F _ x => by
    simp [HahnSeries.algebraMap_apply']
  have hmapC : ∀ x : IsLocalRing.ResidueField A, ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k) (HahnSeries.C x)
      = HahnSeries.C (algebraMap (IsLocalRing.ResidueField A) k x) := fun x => by
    ext n
    by_cases hn : n = 0
    · subst hn; simp [ModularCurve.coeffMap]
    · simp [ModularCurve.coeffMap, hn]
  have hψ₀A : ∀ a : A, ψ₀ (algebraMap A ↥V a) = algebraMap A ↥E' a := by
    intro a
    apply Subtype.ext
    have h1 : algebraMap A ↥V a = ⟨algebraMap A K a, hVA a⟩ := Subtype.ext (halgV a)
    show ψL (algebraMap A ↥V a) = ((algebraMap k ↥E' (algebraMap A k a) : ↥E') : LaurentSeries k)
    rw [h1]
    show ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
        (((θ (IsLocalRing.residue ↥V ⟨algebraMap A K a, hVA a⟩)) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
      = algebraMap k (LaurentSeries k) (algebraMap A k a)
    rw [hθ a, show (((algebraMap (IsLocalRing.ResidueField A) ↥E) (IsLocalRing.residue A a) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
        = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) from rfl,
      hC, hmapC, hκk, hC]
  let ψ : ↥V →ₐ[A] ↥E' := { ψ₀ with commutes' := hψ₀A }
  let Φ : TensorProduct A k ↥V →ₐ[k] ↥E' :=
    Algebra.TensorProduct.lift (Algebra.ofId k ↥E') ψ (fun _ _ => Commute.all _ _)

  have hΦtmul : ∀ (a : k) (v : ↥V), Φ (a ⊗ₜ[A] v) = a • ψ₀ v := fun a v => by
    show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[A] v) = _
    rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
    rfl
  have hΦinj : Function.Injective Φ := by
    by_cases hunitϖ : IsUnit (algebraMap A ↥V ϖ)
    ·
      have h10 : (1 : TensorProduct A k ↥V) = 0 := by
        obtain ⟨u, hu⟩ := hunitϖ
        have h : (1 : k) ⊗ₜ[A] (1 : ↥V) = 0 := by
          have h1 : (1 : ↥V) = algebraMap A ↥V ϖ * ↑u⁻¹ := by rw [← hu, Units.mul_inv]
          rw [h1, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul,
            Algebra.smul_def, hϖ0, zero_mul, TensorProduct.zero_tmul]
        exact h
      haveI : Subsingleton (TensorProduct A k ↥V) := subsingleton_of_zero_eq_one h10.symm
      exact fun x y _ => Subsingleton.elim x y

    have hloc : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥V a ∈ IsLocalRing.maximalIdeal ↥V := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hunitϖ)
    let fκ : (IsLocalRing.ResidueField A) →+* IsLocalRing.ResidueField ↥V :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((IsLocalRing.residue ↥V).comp (algebraMap A ↥V))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hloc a ha))
    letI algκV : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V) := fκ.toAlgebra
    have halgκV : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V) (IsLocalRing.residue A a)
        = IsLocalRing.residue ↥V (algebraMap A ↥V a) := fun a => rfl

    letI algκF : Algebra (IsLocalRing.ResidueField A) ↥E' := ((algebraMap k ↥E').comp (algebraMap (IsLocalRing.ResidueField A) k)).toAlgebra
    haveI : IsScalarTower (IsLocalRing.ResidueField A) k ↥E' := IsScalarTower.of_algebraMap_eq (fun a => rfl)

    let ψκL : IsLocalRing.ResidueField ↥V →+* LaurentSeries k :=
      (ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)).comp ((algebraMap ↥E (LaurentSeries (IsLocalRing.ResidueField A))).comp
        (θ : IsLocalRing.ResidueField ↥V →+* ↥E))
    have hψκL_mem : ∀ r, ψκL r ∈ E' := fun r => IntermediateField.subset_adjoin k S ⟨_, (θ r).2, rfl⟩
    let ψκ₀ : IsLocalRing.ResidueField ↥V →+* ↥E' := ψκL.codRestrict E' hψκL_mem
    have hψκ₀ψ₀ : ∀ v : ↥V, ψκ₀ (IsLocalRing.residue ↥V v) = ψ₀ v := fun v => rfl
    have hψκ₀κ : ∀ r : IsLocalRing.ResidueField A, ψκ₀ (algebraMap (IsLocalRing.ResidueField A) _ r) = algebraMap (IsLocalRing.ResidueField A) ↥E' r := by
      intro r
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
      rw [halgκV, hψκ₀ψ₀, hψ₀A]
      apply Subtype.ext
      show ((algebraMap k ↥E' (algebraMap A k a) : ↥E') : LaurentSeries k)
        = ((algebraMap k ↥E' (algebraMap (IsLocalRing.ResidueField A) k (IsLocalRing.residue A a)) : ↥E') : LaurentSeries k)
      rw [hκk]
    let ψκ : IsLocalRing.ResidueField ↥V →ₐ[IsLocalRing.ResidueField A] ↥E' := { ψκ₀ with commutes' := hψκ₀κ }
    let Φκ : TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) →ₐ[k] ↥E' :=
      Algebra.TensorProduct.lift (Algebra.ofId k ↥E') ψκ (fun _ _ => Commute.all _ _)

    let ρ₀ : ↥V →+* TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) :=
      (Algebra.TensorProduct.includeRight.toRingHom : IsLocalRing.ResidueField ↥V →+* _).comp (IsLocalRing.residue ↥V)
    have hρ₀A : ∀ a : A, ρ₀ (algebraMap A ↥V a) = algebraMap A _ a := by
      intro a
      rw [IsScalarTower.algebraMap_apply A k (TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V))]
      show (1 : k) ⊗ₜ[IsLocalRing.ResidueField A] (IsLocalRing.residue ↥V (algebraMap A ↥V a))
        = algebraMap k (TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V)) (algebraMap A k a)
      rw [← halgκV, ← hκk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    let ρ : ↥V →ₐ[A] TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) := { ρ₀ with commutes' := hρ₀A }
    let π : TensorProduct A k ↥V →ₐ[k] TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) :=
      Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft ρ (fun _ _ => Commute.all _ _)
    have hπtmul : ∀ (a : k) (v : ↥V), π (a ⊗ₜ[A] v) = a ⊗ₜ[IsLocalRing.ResidueField A] IsLocalRing.residue ↥V v := fun a v => by
      show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[A] v) = _
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply]
      show (a ⊗ₜ[IsLocalRing.ResidueField A] (1 : IsLocalRing.ResidueField ↥V)) * ((1 : k) ⊗ₜ[IsLocalRing.ResidueField A] IsLocalRing.residue ↥V v) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

    have hfac : ∀ x, Φ x = Φκ (π x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
        rw [hΦtmul, hπtmul]
        show _ = Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[IsLocalRing.ResidueField A] _)
        rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
        rfl
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

    let σV : IsLocalRing.ResidueField ↥V →+* TensorProduct A k ↥V :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥V)
        (Algebra.TensorProduct.includeRight.toRingHom : ↥V →+* TensorProduct A k ↥V)
        (fun v hv => htmul_maximal v hv)
    have hσV : ∀ v : ↥V, σV (IsLocalRing.residue ↥V v) = (1 : k) ⊗ₜ[A] v := fun v => rfl
    have hπinj : Function.Injective π := by

      have hσVκ : ∀ r : IsLocalRing.ResidueField A, σV (algebraMap (IsLocalRing.ResidueField A) _ r) = algebraMap (IsLocalRing.ResidueField A) (TensorProduct A k ↥V) r := by
        intro r
        obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
        rw [halgκV, hσV, IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField A) k (TensorProduct A k ↥V), hκk,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      let σVa : IsLocalRing.ResidueField ↥V →ₐ[IsLocalRing.ResidueField A] TensorProduct A k ↥V := { σV with commutes' := hσVκ }
      let σ : TensorProduct (IsLocalRing.ResidueField A) k (IsLocalRing.ResidueField ↥V) →ₐ[k] TensorProduct A k ↥V :=
        Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft σVa (fun _ _ => Commute.all _ _)
      have hσπ : ∀ x, σ (π x) = x := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a v =>
          rw [hπtmul]
          show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ[IsLocalRing.ResidueField A] _) = _
          rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply]
          show (a ⊗ₜ[A] (1 : ↥V)) * σV (IsLocalRing.residue ↥V v) = _
          rw [hσV, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      exact fun x y hxy => by rw [← hσπ x, ← hσπ y, hxy]

    have hΦκinj : Function.Injective Φκ := by
      let B := Module.Free.chooseBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥V)
      let BT := Algebra.TensorProduct.basis k B
      have hBT : ∀ i, Φκ (BT i) = ψκ₀ (B i) := fun i => by
        rw [Algebra.TensorProduct.basis_apply]
        show Algebra.TensorProduct.lift _ _ _ _ = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl

      have hθκ : ∀ (c : IsLocalRing.ResidueField A) (r : IsLocalRing.ResidueField ↥V),
          ((θ (c • r) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) = c • ((θ r : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := by
        intro c r
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
        have h1 : algebraMap A ↥V a = ⟨algebraMap A K a, hVA a⟩ := Subtype.ext (halgV a)
        rw [Algebra.smul_def, map_mul, halgκV, h1, hθ a, ← HahnSeries.C_mul_eq_smul, ← hC]
        rfl

      let θL : IsLocalRing.ResidueField ↥V →ₗ[IsLocalRing.ResidueField A] LaurentSeries (IsLocalRing.ResidueField A) :=
        { toFun := fun r => ((θ r : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))
          map_add' := fun x y => by simp only [map_add]; rfl
          map_smul' := fun c r => hθκ c r }
      have hθLinj : LinearMap.ker θL = ⊥ := LinearMap.ker_eq_bot.mpr (fun x y hxy =>
        θ.injective (Subtype.ext hxy))
      have hBθ : LinearIndependent (IsLocalRing.ResidueField A) (fun i => ((θ (B i) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))) :=
        B.linearIndependent.map' θL hθLinj
      have hli : LinearIndependent k (fun i => Φκ (BT i)) := by
        rw [linearIndependent_iff']
        intro s g hsum i hi

        have hval : ∀ j, ((Φκ (BT j) : ↥E') : LaurentSeries k)
            = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k) ((θ (B j) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) := fun j => by
          rw [hBT]; rfl
        have hsum' : ∑ j ∈ s, g j • ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
            ((θ (B j) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) = 0 := by
          have h := congrArg (fun y : ↥E' => (y : LaurentSeries k)) hsum
          rw [AddSubmonoidClass.coe_finset_sum, ZeroMemClass.coe_zero] at h
          rw [← h]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [IntermediateField.coe_smul, Algebra.smul_def, hC, HahnSeries.C_mul_eq_smul, hval]

        let e : Fin s.card ≃ ↥s := s.equivFin.symm
        have hf : LinearIndependent (IsLocalRing.ResidueField A) (fun j : Fin s.card => ((θ (B (e j)) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A))) :=
          hBθ.comp (fun j => ((e j) : _)) (fun j₁ j₂ h => e.injective (Subtype.ext h))
        have hk' := hLD s.card _ hf
        rw [Fintype.linearIndependent_iff] at hk'
        have hz := hk' (fun j => g (e j)) (by
          rw [← hsum']
          rw [← Finset.sum_coe_sort s]
          exact (Equiv.sum_comp e (fun x : ↥s => g x • ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
            ((θ (B x) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)))))
          (e.symm ⟨i, hi⟩)
        simpa using hz

      intro x y hxy
      have hrepr : ∀ z, Φκ z = Finsupp.linearCombination k (fun i => Φκ (BT i)) (BT.repr z) := by
        intro z
        conv_lhs => rw [← BT.linearCombination_repr z]
        rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
        simp only [map_smul]
      rw [hrepr, hrepr] at hxy
      exact BT.repr.injective (hli hxy)
    intro x y hxy
    apply hπinj
    apply hΦκinj
    rw [← hfac, ← hfac, hxy]

  haveI : IsDomain (TensorProduct A k ↥V) := hΦinj.isDomain Φ.toRingHom
  have h𝔮bot : 𝔮 = ⊥ := by
    have hb : (⊥ : Ideal (TensorProduct A k ↥V)).IsPrime := Ideal.isPrime_bot
    exact le_bot_iff.mp (h𝔮.2 ⟨hb, le_rfl⟩ bot_le)

  have hrange_frac : IsFractionRing ↥Φ.range ↥E' := by

    have hS_sub : S ⊆ ((Φ.range).map (IntermediateField.val E') : Set (LaurentSeries k)) := by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨r, hr⟩ := θ.surjective ⟨e, he⟩
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective (R := ↥V) r
      refine ⟨Φ ((1 : k) ⊗ₜ[A] v), ⟨(1 : k) ⊗ₜ[A] v, rfl⟩, ?_⟩
      show ((Φ ((1 : k) ⊗ₜ[A] v) : ↥E') : LaurentSeries k) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      show ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField A) k)
          (((θ (IsLocalRing.residue ↥V v)) : ↥E) : LaurentSeries (IsLocalRing.ResidueField A)) = _
      rw [hr]
    have hadj_le : Algebra.adjoin k S ≤ (Φ.range).map (IntermediateField.val E') := Algebra.adjoin_le hS_sub
    haveI : FaithfulSMul ↥Φ.range ↥E' := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
    refine IsFractionRing.of_field ↥Φ.range ↥E' (fun z => ?_)
    obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
    obtain ⟨x, hx, hxr⟩ := Subalgebra.mem_map.mp (hadj_le hr)
    obtain ⟨y, hy, hys⟩ := Subalgebra.mem_map.mp (hadj_le hs)
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext ?_⟩
    show (z : LaurentSeries k) = ((x / y : ↥E') : LaurentSeries k)
    rw [IntermediateField.coe_div]
    show (z : LaurentSeries k) = (IntermediateField.val E' x) / (IntermediateField.val E' y)
    rw [hxr, hys]
    exact hz

  let e₁ : (TensorProduct A k ↥V ⧸ 𝔮) ≃ₐ[k] TensorProduct A k ↥V :=
    (Ideal.quotientEquivAlgOfEq k h𝔮bot).trans (AlgEquiv.quotientBot k _)
  let e₂ : TensorProduct A k ↥V ≃ₐ[k] ↥Φ.range := AlgEquiv.ofInjective Φ hΦinj
  haveI := hrange_frac
  let Ψ : FractionRing (TensorProduct A k ↥V ⧸ 𝔮) ≃ₐ[k] ↥E' :=
    IsFractionRing.algEquivOfAlgEquiv
      (A := TensorProduct A k ↥V ⧸ 𝔮) (B := ↥Φ.range)
      (K := FractionRing (TensorProduct A k ↥V ⧸ 𝔮)) (L := ↥E') (e₁.trans e₂)
  refine ⟨Ψ, fun v => ?_⟩
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]
  show ((Ψ (algebraMap _ _ (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v))) : ↥E') : LaurentSeries k) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  have he : (e₁.trans e₂) (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) = ⟨Φ ((1 : k) ⊗ₜ[A] v), ⟨(1 : k) ⊗ₜ[A] v, rfl⟩⟩ := by
    apply Subtype.ext
    show ((e₂ (e₁ (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v))) : ↥Φ.range) : ↥E') = Φ ((1 : k) ⊗ₜ[A] v)
    have h1 : e₁ (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[A] v)) = (1 : k) ⊗ₜ[A] v := rfl
    rw [h1]
    rfl
  rw [he]
  show ((Φ ((1 : k) ⊗ₜ[A] v) : ↥E') : LaurentSeries k) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end S_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv
end P2MW
export P2MW.S_ValuationSubring_exists_fractionRing_tensorProduct_quotient_algEquiv_apply_tmul_eq_coeffMap_of_residueField_ringEquiv (solution)
