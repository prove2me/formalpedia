-- Prove2me | solution 1 for Subalgebra.isReduced_tensor_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d8f7f193-1506-5057-bd38-c8360cc5bd3c

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree
import Theorems.Thm_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral
import Theorems.Thm_Polynomial_isReduced_quotient_span_singleton_of_separable_map
import Theorems.Thm_Polynomial_nonempty_ringEquiv_tensor_quotient_span_singleton
import Theorems.Thm_Polynomial_isDomain_tensor_of_isFractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_isReduced_tensor_of_separable

set_option linter.unusedSectionVars false

open Polynomial
open scoped TensorProduct

theorem isReduced_of_ringEquiv' {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) [IsReduced B] :
    IsReduced A := isReduced_of_injective e e.injective

theorem isReduced_of_algHom_injective' {S A B : Type*} [CommSemiring S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) (hf : Function.Injective f) [IsReduced B] :
    IsReduced A := isReduced_of_injective f hf

theorem isReduced_of_injective_map' {A B : Type*} [Semiring A] [Ring B]
    (g : A → B) (hg : Function.Injective g)
    (hadd : ∀ x y : A, g (x + y) = g x + g y) (hmul : ∀ x y : A, g (x * y) = g x * g y)
    (hB : IsReduced B) : IsReduced A := by
  have h0 : g 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact add_right_cancel (this.symm.trans (zero_add _).symm)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    exact eq_zero_of_zero_eq_one hn.symm x
  · have hpow : ∀ m, 0 < m → g (x ^ m) = g x ^ m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => rw [pow_one, pow_one]
      | succ m hm ih => rw [pow_succ, hmul, ih, pow_succ]
    apply hg
    rw [h0]
    exact IsReduced.eq_zero _ ⟨n, by rw [← hpow n hpos, hn, h0]⟩

noncomputable section

namespace GeomReducedAux

open Polynomial TensorProduct

universe u

variable {Λ : Type u} [CommRing Λ] (p₀ : Λ)
variable {K : Type u} [Field K] [Algebra Λ K] (R : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R)
variable (O : Type u) [CommRing O] [Algebra R O] [Algebra O K] [IsScalarTower R O K]
variable (F₀ : Type u) [Field F₀] [Algebra Λ F₀]

abbrev pR : R := algebraMap Λ R p₀

abbrev ϖ : O := algebraMap R O (pR p₀ R)

abbrev κ : Type u := O ⧸ Ideal.span {ϖ p₀ R O}

theorem e_C_p : e (C p₀) = pR p₀ R := by
  rw [← Polynomial.algebraMap_eq]
  exact e.commutes p₀

theorem algebraMap_R_O_injective : Function.Injective (algebraMap R O) := by
  intro x y h
  have := congrArg (algebraMap O K) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  exact Subtype.val_injective this

def toκ₀ : Λ →+* κ p₀ R O :=
  (Ideal.Quotient.mk _).comp ((algebraMap R O).comp (algebraMap Λ R))

variable {p₀ F₀} in

def eF (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) : (Λ ⧸ Ideal.span {p₀}) ≃+* F₀ :=
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs)

variable {p₀ F₀} in
theorem eF_mk (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) (a : Λ) :
    eF hs hker (Ideal.Quotient.mk _ a) = algebraMap Λ F₀ a := rfl

variable {p₀ F₀} in

def liftF₀ (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) : F₀ →+* κ p₀ R O :=
  (Ideal.Quotient.lift (Ideal.span {p₀}) (toκ₀ p₀ R O) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [toκ₀, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))).comp
    (eF hs hker).symm.toRingHom

variable {p₀ F₀} in
theorem liftF₀_algebraMap (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) (a : Λ) :
    liftF₀ R O hs hker (algebraMap Λ F₀ a) =
      Ideal.Quotient.mk _ (algebraMap R O (algebraMap Λ R a)) := by
  rw [liftF₀, RingHom.comp_apply, ← eF_mk hs hker a]
  change Ideal.Quotient.lift _ _ _ ((eF hs hker).symm (eF hs hker (Ideal.Quotient.mk _ a))) = _
  rw [RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  rfl

def xκ : κ p₀ R O := Ideal.Quotient.mk _ (algebraMap R O (e X))

variable {p₀ F₀} in

def toκ (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) : F₀[X] →+* κ p₀ R O :=
  Polynomial.eval₂RingHom (liftF₀ R O hs hker) (xκ p₀ R e O)

variable {p₀ F₀} in
theorem toκ_C (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) (a : F₀) :
    toκ R e O hs hker (C a) = liftF₀ R O hs hker a := by
  simp [toκ]

variable {p₀ F₀} in

theorem toκ_map (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀}) (q : Λ[X]) :
    toκ R e O hs hker (q.map (algebraMap Λ F₀)) = Ideal.Quotient.mk _ (algebraMap R O (e q)) := by
  have h : (toκ R e O hs hker).comp (mapRingHom (algebraMap Λ F₀)) =
      (Ideal.Quotient.mk _).comp ((algebraMap R O).comp (e : Λ[X] →+* R)) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, toκ_C, liftF₀_algebraMap]
      change _ = Ideal.Quotient.mk _ (algebraMap R O (e (C a)))
      rw [← Polynomial.algebraMap_eq, e.commutes]
    · rw [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X, toκ, Polynomial.coe_eval₂RingHom,
        eval₂_X]
      rfl
  exact RingHom.congr_fun h q

variable {p₀ R O} in

theorem mem_span_of_algebraMap_mem (hp : (Ideal.span {pR p₀ R}).IsPrime)
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {pR p₀ R}, ∃ r : R, algebraMap R O r = algebraMap R O s * x)
    {r : R} (hr : algebraMap R O r ∈ Ideal.span {ϖ p₀ R O}) : r ∈ Ideal.span {pR p₀ R} := by
  rw [Ideal.mem_span_singleton'] at hr
  obtain ⟨x, hx⟩ := hr
  obtain ⟨s, hs, r', hr'⟩ := hO x
  have key : s * r = pR p₀ R * r' := by
    apply algebraMap_R_O_injective R O
    rw [map_mul, map_mul, hr', ← hx]
    ring
  have hmem : s * r ∈ Ideal.span {pR p₀ R} := by
    rw [key]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rcases hp.mem_or_mem hmem with h | h
  · exact absurd h hs
  · exact h

variable {p₀ R O} in
theorem algebraMap_notMem_of_notMem (hp : (Ideal.span {pR p₀ R}).IsPrime)
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {pR p₀ R}, ∃ r : R, algebraMap R O r = algebraMap R O s * x)
    {s : R} (hs : s ∉ Ideal.span {pR p₀ R}) : algebraMap R O s ∉ Ideal.span {ϖ p₀ R O} :=
  fun h => hs (mem_span_of_algebraMap_mem hp hO h)

include e in
theorem isPrime_span_pR [IsDomain Λ] (hp₀ : (Ideal.span {p₀}).IsPrime) :
    (Ideal.span {pR p₀ R}).IsPrime := by
  have hCp : (Ideal.span {(C p₀ : Λ[X])}).IsPrime := by
    have := Ideal.isPrime_map_C_of_isPrime (P := Ideal.span {p₀})
    rwa [Ideal.map_span, Set.image_singleton] at this
  have h2 := Ideal.map_isPrime_of_equiv (e : Λ[X] ≃+* R) (I := Ideal.span {(C p₀ : Λ[X])})
  rw [Ideal.map_span, Set.image_singleton] at h2
  convert h2 using 3
  exact (e_C_p p₀ R e).symm

include e in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isReduced_tensor
    [IsDomain Λ] [IsPrincipalIdealRing Λ] (hp₀ : Irreducible p₀)
    (hs : Function.Surjective (algebraMap Λ F₀)) (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p₀})
    (A : Subalgebra Λ K) (hRA : R ≤ A) (hint : ∀ a : A, IsIntegral R (a : K))
    [IsNoetherianRing A] (hIC : IsIntegrallyClosed A)
    [IsDomain O] [IsDiscreteValuationRing O] [FaithfulSMul O K]
    (hpO : Irreducible (ϖ p₀ R O))
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {pR p₀ R}, ∃ r : R, algebraMap R O r = algebraMap R O s * x)
    {α : K} (hα : IsIntegral O α)
    (hαA : ∃ s ∉ Ideal.span {pR p₀ R}, (s : K) * α ∈ A)
    (hsep : ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ p₀ R O}))).Separable)
    (hgen : ∀ x : K, ∃ n : ℕ, algebraMap O K (ϖ p₀ R O) ^ n * x ∈ Algebra.adjoin O {α})
    (k : Type u) [Field k] [Algebra Λ k] [Algebra F₀ k] [IsScalarTower Λ F₀ k] :
    IsReduced (k ⊗[Λ] A) := by
  classical
  haveI hmaxϖ : (Ideal.span {ϖ p₀ R O}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpO
  haveI hmaxp : (Ideal.span {p₀}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp₀
  have hκfield : IsField (κ p₀ R O) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxϖ
  have hpe := e_C_p p₀ R e
  have hp : (Ideal.span {pR p₀ R}).IsPrime := isPrime_span_pR p₀ R e inferInstance
  have hF₀p : algebraMap Λ F₀ p₀ = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _

  letI algF₀κ : Algebra F₀ (κ p₀ R O) := (liftF₀ R O hs hker).toAlgebra
  letI algXκ : Algebra F₀[X] (κ p₀ R O) := (toκ R e O hs hker).toAlgebra
  haveI : IsScalarTower F₀ F₀[X] (κ p₀ R O) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [Polynomial.algebraMap_eq]
    exact (toκ_C R e O hs hker a).symm

  have hinjκ : Function.Injective (algebraMap F₀[X] (κ p₀ R O)) := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective (algebraMap Λ F₀) hs g
    change toκ R e O hs hker _ = 0 at hg
    rw [toκ_map, Ideal.Quotient.eq_zero_iff_mem] at hg
    have h1 : e q ∈ Ideal.span {pR p₀ R} := mem_span_of_algebraMap_mem hp hO hg
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨t, ht⟩ := h1
    have hq : q = e.symm t * C p₀ := e.injective (by rw [map_mul, AlgEquiv.apply_symm_apply, hpe, ht])
    rw [hq, Polynomial.map_mul, Polynomial.map_C, hF₀p, map_zero, mul_zero]
  haveI : IsFractionRing F₀[X] (κ p₀ R O) := by
    rw [IsFractionRing, isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hy0 : algebraMap F₀[X] (κ p₀ R O) y ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero hy (hinjκ (h.trans (map_zero _).symm))
      obtain ⟨b, hb⟩ := hκfield.mul_inv_cancel hy0
      exact IsUnit.of_mul_eq_one _ hb
    · intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨s, hs', r, hr⟩ := hO x
      obtain ⟨qs, rfl⟩ := e.surjective s
      obtain ⟨qr, rfl⟩ := e.surjective r
      have hne : toκ R e O hs hker (qs.map (algebraMap Λ F₀)) ≠ 0 := by
        rw [toκ_map, Ne, Ideal.Quotient.eq_zero_iff_mem]
        exact algebraMap_notMem_of_notMem hp hO hs'
      refine ⟨⟨qr.map (algebraMap Λ F₀), ⟨qs.map (algebraMap Λ F₀),
        mem_nonZeroDivisors_of_ne_zero (fun h => hne (by rw [h, map_zero]))⟩⟩, ?_⟩
      show Ideal.Quotient.mk _ x * toκ R e O hs hker (qs.map (algebraMap Λ F₀)) =
        toκ R e O hs hker (qr.map (algebraMap Λ F₀))
      rw [toκ_map, toκ_map, ← map_mul, hr, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinjκ hxy]⟩
  haveI : IsDomain ((κ p₀ R O) ⊗[F₀] k) := Polynomial.isDomain_tensor_of_isFractionRing F₀ (κ p₀ R O) k

  set f : O[X] := minpoly O α with hfdef
  set B : Subalgebra O K := Algebra.adjoin O {α} with hBdef
  set fbar : (κ p₀ R O)[X] := f.map (Ideal.Quotient.mk (Ideal.span {ϖ p₀ R O})) with hfbar
  have hsq : Squarefree fbar := hsep.squarefree
  haveI hICB : IsIntegrallyClosedIn B K :=
    IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree hpO hα hsq hgen
  let eB : AdjoinRoot f ≃ₐ[O] B := minpoly.equivAdjoin hα
  set J : Ideal B := Ideal.span {algebraMap O B (ϖ p₀ R O)} with hJdef
  have hJmap : (Ideal.span {ϖ p₀ R O}).map (AdjoinRoot.of f) =
      J.map ((eB.symm : B ≃ₐ[O] AdjoinRoot f) : B →+* AdjoinRoot f) := by
    rw [Ideal.map_span, Set.image_singleton, hJdef, Ideal.map_span, Set.image_singleton]
    congr 2
    change algebraMap O (AdjoinRoot f) (ϖ p₀ R O) = eB.symm (algebraMap O B (ϖ p₀ R O))
    rw [AlgEquiv.commutes]
  let β₁ : (B ⧸ J) ≃+* (AdjoinRoot f ⧸ (Ideal.span {ϖ p₀ R O}).map (AdjoinRoot.of f)) :=
    Ideal.quotientEquiv J _ (eB.symm : B ≃ₐ[O] AdjoinRoot f).toRingEquiv hJmap
  let β₂ := (AdjoinRoot.quotEquivQuotMap f (Ideal.span {ϖ p₀ R O})).toRingEquiv
  let β : (B ⧸ J) ≃+* ((κ p₀ R O)[X] ⧸ Ideal.span {fbar}) := β₁.trans β₂
  have hβ : ∀ c : Λ, β (Ideal.Quotient.mk J (algebraMap O B (algebraMap R O (algebraMap Λ R c)))) =
      Ideal.Quotient.mk _ (C (Ideal.Quotient.mk _ (algebraMap R O (algebraMap Λ R c)))) := by
    intro c
    change β₂ (β₁ (Ideal.Quotient.mk J (algebraMap O B (algebraMap R O (algebraMap Λ R c))))) = _
    rw [show β₁ (Ideal.Quotient.mk J (algebraMap O B (algebraMap R O (algebraMap Λ R c)))) =
        Ideal.Quotient.mk _ ((eB.symm : B ≃ₐ[O] AdjoinRoot f) (algebraMap O B (algebraMap R O (algebraMap Λ R c))))
        from Ideal.quotientEquiv_mk _ _ _ _ _]
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
    change AdjoinRoot.quotEquivQuotMap f _ (Ideal.Quotient.mk _ (AdjoinRoot.mk f (C _))) = _
    rw [AdjoinRoot.quotEquivQuotMap_apply_mk, Polynomial.map_C]

  letI algF₀B₀ : Algebra F₀ (B ⧸ J) :=
    ((Ideal.Quotient.lift (Ideal.span {p₀})
      ((Ideal.Quotient.mk J).comp ((algebraMap O B).comp ((algebraMap R O).comp (algebraMap Λ R))))
      (fun a ha => by
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))).comp
      (eF hs hker).symm.toRingHom).toAlgebra
  have halgB₀ : ∀ c : Λ, algebraMap F₀ (B ⧸ J) (algebraMap Λ F₀ c) =
      Ideal.Quotient.mk J (algebraMap O B (algebraMap R O (algebraMap Λ R c))) := by
    intro c
    have hc : (eF hs hker).symm.toRingHom (algebraMap Λ F₀ c) = Ideal.Quotient.mk _ c := by
      rw [← eF_mk hs hker c]
      exact (eF hs hker).symm_apply_apply _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hc, Ideal.Quotient.lift_mk]
    rfl
  let βₐ : (B ⧸ J) ≃ₐ[F₀] ((κ p₀ R O)[X] ⧸ Ideal.span {fbar}) :=
    AlgEquiv.ofRingEquiv (f := β) (fun a => by
      obtain ⟨c, rfl⟩ := hs a
      rw [halgB₀]
      change β _ = _
      rw [hβ, ← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
      congr 2
      exact (liftF₀_algebraMap R O hs hker c).symm)

  haveI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv Λ[X] e.toRingEquiv
  haveI : IsIntegrallyClosed R := by
    haveI : UniqueFactorizationMonoid Λ[X] := inferInstance
    haveI : IsIntegrallyClosed Λ[X] := inferInstance
    exact IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI algRA : Algebra R A := (Subalgebra.inclusion hRA).toRingHom.toAlgebra
  haveI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral R A := ⟨fun a =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A K) Subtype.val_injective).mp (hint a)⟩
  haveI : FaithfulSMul R A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Subalgebra.inclusion_injective hRA
  haveI : IsIntegrallyClosed A := hIC
  have hp0 : pR p₀ R ≠ 0 := by
    rw [← hpe]
    exact fun h => (Polynomial.C_ne_zero.mpr hp₀.ne_zero) (e.injective (h.trans (map_zero e).symm))
  have hmem : ∀ a : A, (a : K) ∈ B := by
    intro a
    have h2 : IsIntegral O (a : K) := (hint a).tower_top
    have h3 : IsIntegral B (a : K) := h2.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral h3
    rw [← hy]
    exact y.2
  let fAB : A →+* B :=
    { toFun := fun a => ⟨a, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hfAB : ∀ a : A, ((fAB a : B) : K) = (a : K) := fun a => rfl
  have hS : ∀ x ∈ Algebra.adjoin O {α}, ∃ r : R, r ∉ Ideal.span {pR p₀ R} ∧ ∃ a : A,
      (a : K) = (r : K) * x := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨s, hs', hsa⟩ := hαA
      exact ⟨s, hs', ⟨_, hsa⟩, rfl⟩
    | algebraMap c =>
      obtain ⟨s, hs', r, hr⟩ := hO c
      refine ⟨s, hs', ⟨r, hRA r.2⟩, ?_⟩
      change (r : K) = (s : K) * algebraMap O K c
      have := congrArg (algebraMap O K) hr
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
      exact this
    | add y z _ _ hy hz =>
      obtain ⟨s, hs', a, ha⟩ := hy
      obtain ⟨t, ht, b, hb⟩ := hz
      refine ⟨s * t, ?_, ⟨t, hRA t.2⟩ * a + ⟨s, hRA s.2⟩ * b, ?_⟩
      · intro hst
        rcases hp.mem_or_mem hst with h | h
        · exact hs' h
        · exact ht h
      · rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, ha, hb, Subalgebra.coe_mul]
        change (t : K) * _ + (s : K) * _ = _
        ring
    | mul y z _ _ hy hz =>
      obtain ⟨s, hs', a, ha⟩ := hy
      obtain ⟨t, ht, b, hb⟩ := hz
      refine ⟨s * t, ?_, a * b, ?_⟩
      · intro hst
        rcases hp.mem_or_mem hst with h | h
        · exact hs' h
        · exact ht h
      · rw [Subalgebra.coe_mul, ha, hb, Subalgebra.coe_mul]
        ring
  set IA : Ideal A := (Ideal.span {p₀}).map (algebraMap Λ A) with hIAdef
  have hIA : IA = Ideal.span {algebraMap R A (pR p₀ R)} := by
    rw [hIAdef, Ideal.map_span, Set.image_singleton]
    rfl
  have hfABp : fAB (algebraMap R A (pR p₀ R)) = algebraMap O B (ϖ p₀ R O) := by
    apply Subtype.ext
    rw [hfAB]
    change ((algebraMap R A (pR p₀ R) : A) : K) = algebraMap O K (algebraMap R O (pR p₀ R))
    rw [← IsScalarTower.algebraMap_apply R O K]
    rfl
  let ι : (A ⧸ IA) →+* (B ⧸ J) :=
    Ideal.Quotient.lift IA ((Ideal.Quotient.mk J).comp fAB) (fun a ha => by
      rw [hIA, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [RingHom.comp_apply, map_mul, hfABp, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJdef,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨s, hs', a', ha'⟩ := hS b b.2
    have hK : (b : K) * algebraMap O K (ϖ p₀ R O) = (a : K) := by
      have := congrArg (fun y : B => (y : K)) hb
      simpa [hfAB] using this
    have hsa : algebraMap R A s * a = algebraMap R A (pR p₀ R) * a' := by
      apply Subtype.ext
      change (s : K) * (a : K) = ((algebraMap R A (pR p₀ R) : A) : K) * (a' : K)
      rw [ha', ← hK]
      change _ = algebraMap R K (pR p₀ R) * _
      rw [IsScalarTower.algebraMap_apply R O K]
      ring
    rw [Ideal.Quotient.eq_zero_iff_mem, hIA]
    apply IsIntegrallyClosed.mem_span_singleton_of_mul_mem_of_isIntegral hp hp0 hs'
    rw [hsa]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  letI algF₀A₀ : Algebra F₀ (A ⧸ IA) :=
    ((algebraMap (Λ ⧸ Ideal.span {p₀}) (A ⧸ IA)).comp (eF hs hker).symm.toRingHom).toAlgebra
  have halgA₀ : ∀ c : Λ, algebraMap F₀ (A ⧸ IA) (algebraMap Λ F₀ c) = Ideal.Quotient.mk IA (algebraMap Λ A c) := by
    intro c
    have hc : (eF hs hker).symm.toRingHom (algebraMap Λ F₀ c) = Ideal.Quotient.mk _ c := by
      rw [← eF_mk hs hker c]
      exact (eF hs hker).symm_apply_apply _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hc]
    exact Ideal.Quotient.algebraMap_quotient_map_quotient c
  haveI : IsScalarTower Λ F₀ (A ⧸ IA) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [halgA₀]; rfl
  let ιₐ : (A ⧸ IA) →ₐ[F₀] (B ⧸ J) :=
    { ι with
      commutes' := fun a => by
        obtain ⟨c, rfl⟩ := hs a
        rw [halgA₀, halgB₀]
        change ι (Ideal.Quotient.mk IA _) = _
        rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
        congr 1
        apply Subtype.ext
        rw [hfAB]
        change ((algebraMap Λ A c : A) : K) = algebraMap O K (algebraMap R O (algebraMap Λ R c))
        rw [← IsScalarTower.algebraMap_apply R O K]
        rfl }
  have hιₐ : Function.Injective ιₐ := hι
  have hT : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) ιₐ) := by
    have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := k) ιₐ.toLinearMap hιₐ
    have h2 : ∀ x, Algebra.TensorProduct.map (AlgHom.id k k) ιₐ x = LinearMap.lTensor k ιₐ.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x y hxy
    apply h1
    rw [← h2, ← h2, hxy]
  have hmonic : fbar.Monic := (minpoly.monic hα).map _

  have hredDX := Polynomial.isReduced_quotient_span_singleton_of_separable_map
    (hmonic.map (algebraMap (κ p₀ R O) ((κ p₀ R O) ⊗[F₀] k))) (hsep.map.map)
  obtain ⟨ePQ⟩ := Polynomial.nonempty_ringEquiv_tensor_quotient_span_singleton (κ p₀ R O)
    ((κ p₀ R O) ⊗[F₀] k) fbar
  have r4 := isReduced_of_injective_map' (fun x => ePQ x) ePQ.injective ePQ.map_add ePQ.map_mul hredDX
  have e3 := (Algebra.TensorProduct.comm F₀ k ((κ p₀ R O)[X] ⧸ Ideal.span {fbar})).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange F₀ (κ p₀ R O) (κ p₀ R O)
        ((κ p₀ R O)[X] ⧸ Ideal.span {fbar}) k).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm (κ p₀ R O) ((κ p₀ R O)[X] ⧸ Ideal.span {fbar}) ((κ p₀ R O) ⊗[F₀] k)).toRingEquiv
  have r3 := isReduced_of_injective_map' (fun x => e3 x) e3.injective e3.map_add e3.map_mul r4
  have eKB := Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := k)) βₐ
  have r2 := isReduced_of_injective_map' (fun x => eKB x) eKB.injective eKB.toRingEquiv.map_add eKB.toRingEquiv.map_mul r3
  have r1 := isReduced_of_injective_map' (fun x => Algebra.TensorProduct.map (AlgHom.id k k) ιₐ x) hT
    (Algebra.TensorProduct.map (AlgHom.id k k) ιₐ).toRingHom.map_add
    (Algebra.TensorProduct.map (AlgHom.id k k) ιₐ).toRingHom.map_mul r2

  let eΛF : (Λ ⧸ Ideal.span {p₀}) ≃ₐ[Λ] F₀ :=
    AlgEquiv.ofRingEquiv (f := eF hs hker) (fun a => eF_mk hs hker a)
  let e2 : (Λ ⧸ Ideal.span {p₀}) ⊗[Λ] A ≃ₐ[Λ] A ⧸ IA :=
    (Algebra.TensorProduct.comm Λ _ A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {p₀})).symm.restrictScalars Λ)
  let eFA : F₀ ⊗[Λ] A ≃ₐ[Λ] A ⧸ IA := (Algebra.TensorProduct.congr eΛF.symm AlgEquiv.refl).trans e2
  let eFA' : F₀ ⊗[Λ] A ≃ₐ[F₀] A ⧸ IA :=
    AlgEquiv.ofRingEquiv (f := eFA.toRingEquiv) (fun a => by
      obtain ⟨c, rfl⟩ := hs a
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact eFA.commutes c)
  have eK1 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := k)) eFA'
  have r0 := isReduced_of_injective_map' (fun x => eK1 x) eK1.injective eK1.toRingEquiv.map_add eK1.toRingEquiv.map_mul r1
  have e1 := (Algebra.TensorProduct.cancelBaseChange Λ F₀ k k A).symm
  exact isReduced_of_injective_map' (fun x => e1 x) e1.injective e1.toRingEquiv.map_add e1.toRingEquiv.map_mul r0

end GeomReducedAux
end

universe u in
open GeomReducedAux in
theorem solution
    {Λ K O F₀ : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [Field K] [Algebra Λ K] (R A : Subalgebra Λ K) (e : Λ[X] ≃ₐ[Λ] R) (hRA : R ≤ A)
    (hint : ∀ a : A, IsIntegral R (a : K)) [IsNoetherianRing A] (hIC : IsIntegrallyClosed A)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra R O] [Algebra O K] [IsScalarTower R O K] [FaithfulSMul O K]
    (hpO : Irreducible (algebraMap R O (algebraMap Λ R p)))
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {algebraMap Λ R p}, ∃ r : R,
      algebraMap R O r = algebraMap R O s * x)
    {α : K} (hα : IsIntegral O α)
    (hαA : ∃ s ∉ Ideal.span {algebraMap Λ R p}, (s : K) * α ∈ A)
    (hsep : ((minpoly O α).map (Ideal.Quotient.mk
      (Ideal.span {algebraMap R O (algebraMap Λ R p)}))).Separable)
    (hgen : ∀ x : K, ∃ n : ℕ,
      algebraMap O K (algebraMap R O (algebraMap Λ R p)) ^ n * x ∈ Algebra.adjoin O {α})
    [Field F₀] [Algebra Λ F₀] (hs : Function.Surjective (algebraMap Λ F₀))
    (hker : RingHom.ker (algebraMap Λ F₀) = Ideal.span {p})
    (k : Type u) [Field k] [Algebra Λ k] [Algebra F₀ k] [IsScalarTower Λ F₀ k] :
    IsReduced (k ⊗[Λ] A) :=
  GeomReducedAux.isReduced_tensor p R e O F₀ hp hs hker A hRA hint hIC hpO hO hα hαA hsep hgen k

end S_Subalgebra_isReduced_tensor_of_separable
end P2MW
export P2MW.S_Subalgebra_isReduced_tensor_of_separable (solution)
