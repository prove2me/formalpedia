-- Prove2me | solution 1 for PDivisibleGroup.exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f24ce14f-f612-5706-9387-8fb1161c8819

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvPowerSeries_exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates

set_option autoImplicit false

open MvPowerSeries
open scoped TensorProduct

universe u v

namespace H4dLaw

section Coeff

variable {R : Type*} [CommRing R] {d : ℕ}

private noncomputable def zfam (d : ℕ) (R : Type*) [CommRing R] :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d) R :=
  Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) fun _ => 0

private theorem constantCoeff_zfam (s : Fin d ⊕ Fin d) : (zfam d R s).constantCoeff = 0 := by
  rcases s with l | l
  · exact constantCoeff_X l
  · exact map_zero _

private theorem hasSubst_zfam : HasSubst (zfam d R) :=
  hasSubst_of_constantCoeff_zero constantCoeff_zfam

private theorem prod_pow_comp_inl :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inl)
      = fun (l : Fin d) (e : ℕ) => (X l : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem prod_pow_comp_inr :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inr)
      = fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem coeff_subst_zfam (g : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d →₀ ℕ) :
    coeff m (subst (zfam d R) g) = coeff (m.sumElim 0) g := by
  classical
  rw [coeff_subst hasSubst_zfam, finsum_eq_single _ (m.sumElim (0 : Fin d →₀ ℕ))]
  · rw [Finsupp.prod_sumElim, prod_pow_comp_inl, Finsupp.prod_zero_index, mul_one,
      ← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro n hn
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, n = a.sumElim b :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain n).symm⟩
    rw [Finsupp.prod_sumElim, prod_pow_comp_inl, prod_pow_comp_inr]
    by_cases hb : b = 0
    · subst hb
      have hab : m ≠ a := fun h => hn (by rw [h])
      rw [Finsupp.prod_zero_index, mul_one, ← MvPowerSeries.monomial_one_eq,
        coeff_monomial_ne hab, smul_zero]
    · obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (Finsupp.ext h)
      have hz : (b.prod fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr ht) (zero_pow ht)
      rw [hz, mul_zero, map_zero, smul_zero]

end Coeff

private theorem algHom_ext_X {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S] {τ : Type*} [Finite τ]
    {ψ ψ' : MvPowerSeries τ R →ₐ[R] S} (hψ : ∀ s, ψ (X s) ∈ J.radical)
    (h : ∀ s, ψ (X s) = ψ' (X s)) : ψ = ψ' := by
  apply AlgHom.ext
  intro f
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ hψ f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ'
      (fun s => h s ▸ hψ s) f]
  congr 1
  funext s
  exact h s

section Unit

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]

private theorem map_id_counitAlgHom_comul (a : A) :
    Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A)
      (Coalgebra.comul (R := 𝓞) a) = a ⊗ₜ[𝓞] (1 : 𝓞) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A)).toLinearMap
      = LinearMap.lTensor A (Coalgebra.counit (R := 𝓞) (A := A)) := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have h2 := LinearMap.congr_fun h (Coalgebra.comul (R := 𝓞) a)
  rw [AlgHom.toLinearMap_apply] at h2
  rw [h2, Coalgebra.lTensor_counit_comul]

private theorem pi_subst_zfam_eq [IsAdicComplete (Ideal.span {(p : A)}) A]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (hxε : ∀ j, Coalgebra.counit (R := 𝓞) (x j) = 0)
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] A) (hπX : ∀ j, π (X j) = x j)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π (subst (zfam d 𝓞) (F i)) = x i := by
  have heq : π.comp (substAlgHom (hasSubst_zfam (d := d) (R := 𝓞)))
      = ((Algebra.TensorProduct.rid 𝓞 𝓞 A).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A))).comp π₂ := by
    apply algHom_ext_X (Ideal.span {(p : A)})
    · rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam]
        show π (X j) ∈ _
        rw [hπX]
        exact hxrad j
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam]
        show π 0 ∈ _
        rw [map_zero]
        exact Ideal.zero_mem _
    · rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam, AlgHom.comp_apply,
          AlgHom.comp_apply, hπ₂X]
        show π (X j) = _
        rw [hπX]
        simp
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam, AlgHom.comp_apply,
          AlgHom.comp_apply, hπ₂X]
        show π 0 = _
        rw [map_zero]
        simp [hxε]
  have h := AlgHom.congr_fun heq (F i)
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply, AlgHom.comp_apply, hFΔ,
    map_id_counitAlgHom_comul] at h
  rw [h]
  simp

end Unit

section Pair

variable {𝓞 : Type u} [CommRing 𝓞]

private theorem pairTower (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)]
    [∀ v, Module.Free 𝓞 (R v)] [∀ v, Module.Finite 𝓞 (R v)]
    (t : ∀ v, R (v + 1) →ₐ[𝓞] R v)
    {σ : Type} [Finite σ] (x : ∀ v, σ → R v) (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N)
    (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)]
    [∀ v, Module.Free 𝓞 (R' v)] [∀ v, Module.Finite 𝓞 (R' v)]
    (t' : ∀ v, R' (v + 1) →ₐ[𝓞] R' v)
    {σ' : Type} [Finite σ'] (x' : ∀ v, σ' → R' v) (hxt' : ∀ v i, t' v (x' (v + 1) i) = x' v i)
    (hxrad' : ∀ v i, x' v i ∈ (Ideal.span {(p : R' v)}).radical)
    (hxsurj' : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)))
    (hxker' : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ^ N) :
    ((∀ v s, Algebra.TensorProduct.map (t v) (t' v)
        (Sum.elim (fun i => x (v + 1) i ⊗ₜ[𝓞] (1 : R' (v + 1)))
          (fun i => (1 : R (v + 1)) ⊗ₜ[𝓞] x' (v + 1) i) s) =
      Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
    (∀ v s, Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s ∈
      (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
    (∀ v, Function.Surjective
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v))) ∧
    (∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v)) ≤
      (Ideal.span (Set.range
        (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p)))) ^ N)) ∧
    ∃ π : ∀ v, MvPowerSeries (σ ⊕ σ') 𝓞 →ₐ[𝓞] R v ⊗[𝓞] R' v,
      (∀ v s, π v (X s) =
        Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (Algebra.TensorProduct.map (t v) (t' v)).comp (π (v + 1)) = π v) ∧
      (∀ v s, π v (X s) ∈ (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
      (∀ v G, π v G =
        MvFormalGroup.adicEval (Ideal.span {(p : R v ⊗[𝓞] R' v)}) (fun s => π v (X s)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R v ⊗[𝓞] R' v,
        (∀ v, Algebra.TensorProduct.map (t v) (t' v) (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    Algebra.TensorProduct.specialFibre_coordinates_sumElim_tmul (𝓞 := 𝓞) p R t x hxt hxrad hxsurj
      hxker R' t' x' hxt' hxrad' hxsurj' hxker'
  obtain ⟨π, a1, a2, a3, a4, a5, a6, a7⟩ :=
    MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates (𝓞 := 𝓞)
      p hp hker (fun v => R v ⊗[𝓞] R' v) (fun v => Algebra.TensorProduct.map (t v) (t' v))
      (fun v => Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i))
      h1 h2 h3 h4
  exact ⟨⟨h1, h2, h3, h4⟩, π, a1, a2, a3, a4, a5, a6, a7⟩

end Pair

end H4dLaw

namespace H4dS4

section Aux

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Algebra 𝓞 A]

private theorem tmul_one_mem_radical {B : Type*} [CommRing B] [Algebra 𝓞 B] {a : A}
    (ha : a ∈ (Ideal.span {(p : A)}).radical) :
    a ⊗ₜ[𝓞] (1 : B) ∈ (Ideal.span {(p : A ⊗[𝓞] B)}).radical := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc,
    show (c * (p : A)) ⊗ₜ[𝓞] (1 : B) = (c ⊗ₜ[𝓞] (1 : B)) * ((p : A) ⊗ₜ[𝓞] (1 : B)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
    ← Algebra.TensorProduct.natCast_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem one_tmul_mem_radical {B : Type*} [CommRing B] [Algebra 𝓞 B] {b : B}
    (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    (1 : A) ⊗ₜ[𝓞] b ∈ (Ideal.span {(p : A ⊗[𝓞] B)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc,
    show (1 : A) ⊗ₜ[𝓞] (c * (p : B)) = ((1 : A) ⊗ₜ[𝓞] c) * ((1 : A) ⊗ₜ[𝓞] (p : B)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
    ← Algebra.TensorProduct.natCast_def']
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem algHom_eq_of_forall_X {S : Type*} [CommRing S] [Algebra 𝓞 S] (J : Ideal S)
    [IsAdicComplete J S] {τ : Type*} [Finite τ] (ψ₁ ψ₂ : MvPowerSeries τ 𝓞 →ₐ[𝓞] S)
    (hX : ∀ s, ψ₁ (X s) = ψ₂ (X s)) (hrad : ∀ s, ψ₂ (X s) ∈ J.radical) (f : MvPowerSeries τ 𝓞) :
    ψ₁ f = ψ₂ f := by
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₁
      (fun s => (hX s).symm ▸ hrad s) f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₂ hrad f]
  congr 1
  funext s
  exact hX s

end Aux

private theorem pi2_subst_swap_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {A : Type v} [CommRing A] [Bialgebra 𝓞 A] [Coalgebra.IsCocomm 𝓞 A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] A)}) (A ⊗[𝓞] A)]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π₂ (subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        fun j => X (Sum.inl j))
      (F i)) = π₂ (F i) := by
  classical
  set sw : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
    Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) fun j => X (Sum.inl j)
    with hsw
  have hsw0 : ∀ s, constantCoeff (sw s) = 0 := by
    rintro (j | j) <;> simp [hsw, constantCoeff_X]
  have hswS : HasSubst sw := hasSubst_of_constantCoeff_zero hsw0
  let ψ₁ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A := π₂.comp (substAlgHom hswS)
  let ψ₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A :=
    (Algebra.TensorProduct.comm 𝓞 A A).toAlgHom.comp π₂
  have hψ₁ : ∀ G, ψ₁ G = π₂ (subst sw G) := fun G => by
    simp only [ψ₁, AlgHom.comp_apply, substAlgHom_apply]
  have hψ₂ : ∀ G, ψ₂ G = Algebra.TensorProduct.comm 𝓞 A A (π₂ G) := fun G => rfl
  have hX : ∀ s, ψ₁ (X s) = ψ₂ (X s) := by
    rintro (j | j)
    · rw [hψ₁, hψ₂, subst_X hswS, hsw, Sum.elim_inl, hπ₂X, hπ₂X, Sum.elim_inr, Sum.elim_inl,
        Algebra.TensorProduct.comm_tmul]
    · rw [hψ₁, hψ₂, subst_X hswS, hsw, Sum.elim_inr, hπ₂X, hπ₂X, Sum.elim_inl, Sum.elim_inr,
        Algebra.TensorProduct.comm_tmul]
  have hrad : ∀ s, ψ₂ (X s) ∈ (Ideal.span {(p : A ⊗[𝓞] A)}).radical := by
    rintro (j | j)
    · rw [hψ₂, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.comm_tmul]
      exact one_tmul_mem_radical p (hxrad j)
    · rw [hψ₂, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.comm_tmul]
      exact tmul_one_mem_radical p (hxrad j)
  have key := algHom_eq_of_forall_X (Ideal.span {(p : A ⊗[𝓞] A)}) ψ₁ ψ₂ hX hrad (F i)
  rw [hψ₁, hψ₂, hFΔ] at key
  rw [key, hFΔ]
  exact Coalgebra.comm_comul 𝓞 (x i)

section AuxA

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    f b ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem assoc_apply_eq (z : (A ⊗[𝓞] A) ⊗[𝓞] A) :
    Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A z = _root_.TensorProduct.assoc 𝓞 A A A z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul w c =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | tmul a b => rw [Algebra.TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
    | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, map_add, hu, hu']
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem map_includeLeft_eq_assoc (z : A ⊗[𝓞] A) :
    Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A) z =
      Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A (z ⊗ₜ[𝓞] (1 : A)) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.zero_tmul, map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.assoc_tmul]
  | add a b ha hb => rw [map_add, ha, hb, TensorProduct.add_tmul, map_add]

end AuxA

section Assoc

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]
  [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))}) (A ⊗[𝓞] (A ⊗[𝓞] A))]
  {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
  (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
  (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
  (π₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A))
  (hπ₃X : ∀ s, π₃ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A ⊗[𝓞] A))
    (fun s' => (1 : A) ⊗ₜ[𝓞] Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s') s)
  (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hF0 : ∀ i, (F i).constantCoeff = 0)
  (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i))

private noncomputable abbrev β (𝓞 : Type u) [CommRing 𝓞] (d : ℕ) :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 :=
  Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun l => X (Sum.inr (Sum.inl l))

private noncomputable abbrev γ (𝓞 : Type u) [CommRing 𝓞] (d : ℕ) :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 :=
  Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun l => X (Sum.inr (Sum.inr l))

omit [Bialgebra 𝓞 A] in
private theorem hasSubst_β : HasSubst (β 𝓞 d) :=
  hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> simp [constantCoeff_X])

omit [Bialgebra 𝓞 A] in
private theorem hasSubst_γ : HasSubst (γ 𝓞 d) :=
  hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> simp [constantCoeff_X])

include hF0 in
omit [Bialgebra 𝓞 A] in
private theorem hasSubst_αL : HasSubst (Sum.elim (fun j => subst (β 𝓞 d) (F j))
    fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · rw [Sum.elim_inl]
    exact constantCoeff_subst_eq_zero (hasSubst_β (𝓞 := 𝓞) (d := d))
      (by rintro (l | l) <;> simp [constantCoeff_X]) (hF0 j)
  · rw [Sum.elim_inr, constantCoeff_X]

include hF0 in
omit [Bialgebra 𝓞 A] in
private theorem hasSubst_αR : HasSubst (Sum.elim
    (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun j => subst (γ 𝓞 d) (F j)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · rw [Sum.elim_inl, constantCoeff_X]
  · rw [Sum.elim_inr]
    exact constantCoeff_subst_eq_zero (hasSubst_γ (𝓞 := 𝓞) (d := d))
      (by rintro (l | l) <;> simp [constantCoeff_X]) (hF0 j)

include hxrad hπ₂X hπ₃X in

private theorem pi3_subst_β (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (β 𝓞 d) G) =
      Algebra.TensorProduct.map (AlgHom.id 𝓞 A)
        (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_β (𝓞 := 𝓞) (d := d))))
    ((Algebra.TensorProduct.map (AlgHom.id 𝓞 A)
      (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A)).comp π₂)
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_β (𝓞 := 𝓞) (d := d)), β, Sum.elim_inl, hπ₃X, Sum.elim_inl,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.one_def]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_β (𝓞 := 𝓞) (d := d)), β, Sum.elim_inr, hπ₃X, Sum.elim_inr,
          Sum.elim_inl, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply])
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply]
        exact tmul_one_mem_radical p (hxrad l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply]
        exact one_tmul_mem_radical p (tmul_one_mem_radical p (hxrad l))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X in

private theorem pi3_subst_γ (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (γ 𝓞 d) G) =
      (Algebra.TensorProduct.includeRight : A ⊗[𝓞] A →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A)) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_γ (𝓞 := 𝓞) (d := d))))
    ((Algebra.TensorProduct.includeRight : A ⊗[𝓞] A →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A)).comp π₂)
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_γ (𝓞 := 𝓞) (d := d)), γ, Sum.elim_inl, hπ₃X, Sum.elim_inr,
          Sum.elim_inl, AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.includeRight_apply]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_γ (𝓞 := 𝓞) (d := d)), γ, Sum.elim_inr, hπ₃X, Sum.elim_inr,
          Sum.elim_inr, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply])
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.includeRight_apply]
        exact one_tmul_mem_radical p (tmul_one_mem_radical p (hxrad l))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply]
        exact one_tmul_mem_radical p (one_tmul_mem_radical p (hxrad l))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X hF0 hFΔ in

private theorem pi3_subst_αL (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (Sum.elim (fun j => subst (β 𝓞 d) (F j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞)) G) =
      ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A))) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_αL (𝓞 := 𝓞) F hF0)))
    (((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A))).comp π₂)
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αL (𝓞 := 𝓞) F hF0), Sum.elim_inl, pi3_subst_β p x hxrad π₂ hπ₂X π₃ hπ₃X,
          hFΔ, map_includeLeft_eq_assoc, AlgHom.comp_apply, hπ₂X, Sum.elim_inl, AlgHom.comp_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
        rfl
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αL (𝓞 := 𝓞) F hF0), Sum.elim_inr, hπ₃X, Sum.elim_inr, Sum.elim_inr,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comul_one]
        change _ = Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A (((1 : A) ⊗ₜ[𝓞] (1 : A)) ⊗ₜ[𝓞] x j)
        rw [Algebra.TensorProduct.assoc_tmul])
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl]
        exact map_mem_radical p _ (tmul_one_mem_radical p (hxrad j))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr]
        exact map_mem_radical p _ (one_tmul_mem_radical p (hxrad j))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X hF0 hFΔ in

private theorem pi3_subst_αR (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (Sum.elim (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
      fun j => subst (γ 𝓞 d) (F j)) G) =
      (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A)) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_αR (𝓞 := 𝓞) F hF0)))
    ((Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A)).comp π₂)
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αR (𝓞 := 𝓞) F hF0), Sum.elim_inl, hπ₃X, Sum.elim_inl,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Bialgebra.comulAlgHom_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αR (𝓞 := 𝓞) F hF0), Sum.elim_inr, pi3_subst_γ p x hxrad π₂ hπ₂X π₃ hπ₃X,
          hFΔ, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply])
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl]
        exact map_mem_radical p _ (tmul_one_mem_radical p (hxrad j))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr]
        exact map_mem_radical p _ (one_tmul_mem_radical p (hxrad j))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

end Assoc

private theorem pi3_subst_assoc_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {A : Type v} [CommRing A] [Bialgebra 𝓞 A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] A)}) (A ⊗[𝓞] A)]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))}) (A ⊗[𝓞] (A ⊗[𝓞] A))]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (π₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A))
    (hπ₃X : ∀ s, π₃ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A ⊗[𝓞] A))
      (fun s' => (1 : A) ⊗ₜ[𝓞] Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s') s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hF0 : ∀ i, (F i).constantCoeff = 0)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π₃ (subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inl l)))
          (F j))
        fun j => X (Sum.inr (Sum.inr j)))
      (F i)) =
    π₃ (subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inr l)))
          (F j))
      (F i)) := by
  rw [pi3_subst_αL p x hxrad π₂ hπ₂X π₃ hπ₃X F hF0 hFΔ, pi3_subst_αR p x hxrad π₂ hπ₂X π₃ hπ₃X F hF0 hFΔ, hFΔ]

  have hL : ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A)))
        (Coalgebra.comul (R := 𝓞) (x i)) =
      _root_.TensorProduct.assoc 𝓞 A A A
        ((Coalgebra.comul (R := 𝓞) (A := A)).rTensor A (Coalgebra.comul (R := 𝓞) (x i))) := by
    generalize Coalgebra.comul (R := 𝓞) (x i) = z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b =>
      rw [LinearMap.rTensor_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Bialgebra.comulAlgHom_apply, ← assoc_apply_eq]
      rfl
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]
  have hR : (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A))
        (Coalgebra.comul (R := 𝓞) (x i)) =
      (Coalgebra.comul (R := 𝓞) (A := A)).lTensor A (Coalgebra.comul (R := 𝓞) (x i)) := by
    generalize Coalgebra.comul (R := 𝓞) (x i) = z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  rw [hL, hR]
  exact Coalgebra.coassoc_apply (x i)

end H4dS4

open H4dLaw in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v)
    (d : ℕ) (x : ∀ v, Fin d → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxε : ∀ v i, Coalgebra.counit (R := 𝓞) (x v i) = 0)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) :
    ∃ (F : MvFormalGroup d 𝓞) (_ : F.IsComm) (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v),
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) ∧
      (∀ v i, Coalgebra.counit (R := 𝓞) (π v (X i)) = 0) ∧
      (∀ v i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
          (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
          (F.toPowerSeries i)) := by
  classical

  haveI hc1 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  haveI hc2 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)}) (R₀ v ⊗[𝓞] R₀ v) :=
    fun v => IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v ⊗[𝓞] R₀ v)
  haveI hc3 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v))})
      (R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v)) :=
    fun v => IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v))

  have hxt₁ : ∀ v i, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v) (x (v + 1) i) = x v i := fun v i => by
    rw [BialgHom.coe_toAlgHom]
    exact hxt v i

  obtain ⟨π, hπX, hπsurj, hπcomp, hπrad, hπeval, hπinj, hπjs⟩ :=
    MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates (𝓞 := 𝓞) p hp hker R₀
      (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad hxsurj hxker

  obtain ⟨⟨h2t, h2rad, h2surj, h2ker⟩, π₂, hπ₂X, -, -, -, hπ₂eval, hπ₂inj, hπ₂js⟩ :=
    pairTower (𝓞 := 𝓞) p hp hker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad
      hxsurj hxker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad hxsurj hxker
  obtain ⟨-, π₃, hπ₃X, -, -, -, -, hπ₃inj, -⟩ :=
    pairTower (𝓞 := 𝓞) p hp hker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad
      hxsurj hxker (fun v => R₀ v ⊗[𝓞] R₀ v)
      (fun v => Algebra.TensorProduct.map (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)
        (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v))
      (fun v => Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R₀ v)) (fun i => (1 : R₀ v) ⊗ₜ[𝓞] x v i))
      h2t h2rad h2surj h2ker

  have hz : ∀ i v, Algebra.TensorProduct.map (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)
      (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v) (Coalgebra.comul (R := 𝓞) (x (v + 1) i))
      = Coalgebra.comul (R := 𝓞) (x v i) := by
    intro i v
    have h := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom (t₀ v)) (x (v + 1) i)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, BialgHom.coe_toAlgHom, hxt] at h
    exact h
  choose F hF using fun i => hπ₂js (fun v => Coalgebra.comul (R := 𝓞) (x v i)) (hz i)

  have hunit : ∀ i, subst (zfam d 𝓞) (F i) = X i := fun i => by
    refine sub_eq_zero.mp (hπinj _ fun v => ?_)
    rw [map_sub, hπX, pi_subst_zfam_eq p (x v) (hxrad v) (hxε v) (π v) (hπX v) (π₂ v) (hπ₂X v)
      F (fun i => hF i v) i, sub_self]
  have hF0 : ∀ i, (F i).constantCoeff = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← Finsupp.sumElim_zero_zero, ← coeff_subst_zfam,
      hunit, coeff_zero_X]
  have hinl : ∀ i j, (F i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0 := by
    intro i j
    rw [← Finsupp.sumElim_single_zero, ← coeff_subst_zfam, hunit, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hcomm : ∀ i, subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
      fun j => X (Sum.inl j)) (F i) = F i := fun i => by
    refine sub_eq_zero.mp (hπ₂inj _ fun v => ?_)
    rw [map_sub, H4dS4.pi2_subst_swap_eq p (x v) (hxrad v) (π₂ v) (hπ₂X v) F (fun i => hF i v) i,
      sub_self]
  have hassoc : ∀ i,
      subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
              fun l => X (Sum.inr (Sum.inl l)))
            (F j))
          fun j => X (Sum.inr (Sum.inr j)))
        (F i)
        =
      subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
              fun l => X (Sum.inr (Sum.inr l)))
            (F j))
        (F i) := fun i => by
    refine sub_eq_zero.mp (hπ₃inj _ fun v => ?_)
    rw [map_sub, H4dS4.pi3_subst_assoc_eq p (x v) (hxrad v) (π₂ v) (hπ₂X v) (π₃ v) (hπ₃X v) F hF0
      (fun i => hF i v) i, sub_self]

  have hinr : ∀ i j, (F i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0 := by
    intro i j
    have hc0 : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
      rintro (s | s) <;> exact constantCoeff_X _
    rw [← hcomm i, MvFormalGroup.coeff_single_subst hc0 (F i) (Sum.inr j), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X, Sum.inr.injEq, reduceCtorEq,
      if_false, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hinl i j

  let Flaw : MvFormalGroup d 𝓞 :=
    { toPowerSeries := F
      constantCoeff_eq_zero := hF0
      coeff_single_inl := hinl
      coeff_single_inr := hinr
      assoc := hassoc }
  refine ⟨Flaw, ⟨hcomm⟩, π, hπX, hπsurj, hπcomp, hπrad, hπeval, hπinj, hπjs, fun v i => ?_,
    fun v i => ?_⟩
  · rw [hπX]
    exact hxε v i
  · simp only [hπX]
    rw [← hF i v, hπ₂eval v (F i)]
    congr 1
    funext s
    rcases s with j | j
    · rw [hπ₂X]
    · rw [hπ₂X]

end S_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates
end P2MW
export P2MW.S_PDivisibleGroup_exists_mvFormalGroup_comul_eq_adicEval_of_specialFibre_coordinates (solution)
