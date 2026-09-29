-- Prove2me | solution 1 for PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9d2c55da-b67a-590a-9488-e210ee092752

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
import Theorems.Thm_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

universe u v

open scoped TensorProduct
open PDivisibleGroup.Hopf

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.torsionIdeal transition level mk finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal"
namespace ConnTower
p2m_open "PDivisibleGroup"

section Descent

variable {R : Type*} [CommRing R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

private theorem exists_bialgHom_comp_eq (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    (ψ : A →ₐc[R] C)
    (hker : RingHom.ker (π : A →ₐ[R] B) ≤ RingHom.ker (ψ : A →ₐ[R] C)) :
    ∃ χ : B →ₐc[R] C, χ.comp π = ψ := by
  let χ₀ : B →ₐ[R] C := AlgHom.liftOfSurjective (π : A →ₐ[R] B) hπ (ψ : A →ₐ[R] C) hker
  have hχ₀ : χ₀.comp (π : A →ₐ[R] B) = (ψ : A →ₐ[R] C) := AlgHom.liftOfSurjective_comp _ _ _ _
  have hχ₀' : ∀ a, χ₀ (π a) = ψ a := fun a => DFunLike.congr_fun hχ₀ a
  have hπ' : Function.Surjective (π : A →ₐ[R] B) := hπ
  refine ⟨BialgHom.ofAlgHom χ₀ ?_ ?_, ?_⟩
  · refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hπ' b
    change Coalgebra.counit (R := R) (χ₀ (π a)) = Coalgebra.counit (R := R) (π a)
    rw [hχ₀', CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  · refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hπ' b
    change Algebra.TensorProduct.map χ₀ χ₀ (Coalgebra.comul (R := R) (π a)) =
      Coalgebra.comul (R := R) (χ₀ (π a))
    rw [hχ₀', ← CoalgHomClass.map_comp_comul_apply π a]
    change Algebra.TensorProduct.map χ₀ χ₀
        (TensorProduct.map (π : A →ₐ[R] B).toLinearMap (π : A →ₐ[R] B).toLinearMap
          (Coalgebra.comul (R := R) a)) = Coalgebra.comul (R := R) (ψ a)
    rw [← CoalgHomClass.map_comp_comul_apply ψ a]
    change _ = TensorProduct.map (ψ : A →ₐ[R] C).toLinearMap (ψ : A →ₐ[R] C).toLinearMap
      (Coalgebra.comul (R := R) a)
    induction (Coalgebra.comul (R := R) a) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      change χ₀ (π x) ⊗ₜ[R] χ₀ (π y) = ψ x ⊗ₜ[R] ψ y
      rw [hχ₀', hχ₀']
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  · ext a
    exact hχ₀' a

end Descent

section Idempotents

variable {A : Type*} [CommRing A]

private theorem eq_zero_or_eq_one_of_isIdempotentElem [IsLocalRing A] {e : A}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).1 he)
  · left
    have h1 : (1 - e) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit h).1 he.one_sub
    have := congrArg (fun x => 1 - x) h1
    simpa using this

private theorem apply_eq_one_of_isIdempotentElem {B : Type*} [CommRing B] [IsLocalRing B]
    {S : Type*} [CommRing S] [Nontrivial S]
    (ρ : A →+* B) {e : A} (he : IsIdempotentElem e) (ε : B →+* S) (hε : ε (ρ e) = 1) :
    ρ e = 1 := by
  rcases eq_zero_or_eq_one_of_isIdempotentElem (he.map ρ) with h | h
  · rw [h, map_zero] at hε
    exact absurd hε zero_ne_one
  · exact h

private theorem isIdempotentElem_unique {S : Type*} [CommRing S] [Nontrivial S] (ε : A →+* S)
    {f g : A} (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hεf : ε f = 1) (hεg : ε g = 1)
    (hlf : IsLocalRing (A ⧸ Ideal.span {1 - f})) (hlg : IsLocalRing (A ⧸ Ideal.span {1 - g})) :
    f = g := by

  have key : ∀ {f g : A}, IsIdempotentElem f → IsIdempotentElem g → ε f = 1 → ε g = 1 →
      IsLocalRing (A ⧸ Ideal.span {1 - f}) → f = f * g := by
    intro f g hf hg hεf hεg hlf

    rcases eq_zero_or_eq_one_of_isIdempotentElem (hg.map (Ideal.Quotient.mk (Ideal.span {1 - f})))
      with h | h
    ·
      exfalso
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
      have hfg : f * g = 0 := by
        rw [← ha]
        calc f * (a * (1 - f)) = a * (f - f * f) := by ring
          _ = 0 := by rw [hf.eq, sub_self, mul_zero]
      have := congrArg ε hfg
      rw [map_mul, hεf, hεg, mul_one, map_zero] at this
      exact one_ne_zero this
    ·
      have h' : (1 : A) - g ∈ Ideal.span {1 - f} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h, sub_self]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h'
      have h0 : f * (1 - g) = 0 := by
        rw [← ha]
        calc f * (a * (1 - f)) = a * (f - f * f) := by ring
          _ = 0 := by rw [hf.eq, sub_self, mul_zero]
      rw [mul_sub, mul_one, sub_eq_zero] at h0
      exact h0
  rw [key hf hg hεf hεg hlf, mul_comm]
  exact (key hg hf hεg hεf hlg).symm

end Idempotents

section Ideals

variable {R : Type*} [CommRing R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

private theorem ideal_map_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (I : Ideal A) :
    I.map (g.comp f) = (I.map f).map g :=
  (Ideal.map_map (f : A →+* B) (g : B →+* C)).symm

private theorem map_augIdeal_eq_of_surjective [Bialgebra R A] [Bialgebra R B] (φ : A →ₐc[R] B)
    (hφ : Function.Surjective φ) :
    (augIdeal R A).map (φ : A →ₐ[R] B) = augIdeal R B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_augIdeal_iff]
    change Coalgebra.counit (R := R) (φ a) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff R A a).1 ha
  · intro b hb
    have hφ' : Function.Surjective (φ : A →ₐ[R] B) := hφ
    obtain ⟨a, rfl⟩ := hφ' b
    have ha : a - algebraMap R A (Coalgebra.counit (R := R) a) ∈ augIdeal R A :=
      sub_algebraMap_counit_mem_augIdeal R A a
    have hεa : Coalgebra.counit (R := R) a = 0 := by
      have hb' := (mem_augIdeal_iff R B _).1 hb
      change Coalgebra.counit (R := R) (φ a) = 0 at hb'
      rwa [CoalgHomClass.counit_comp_apply] at hb'
    rw [hεa, map_zero, sub_zero] at ha
    exact Ideal.mem_map_of_mem _ ha

private theorem map_torsionIdeal_eq_of_surjective [Bialgebra R A] [Bialgebra R B]
    (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) (n : ℕ) :
    (torsionIdeal R A n).map (φ : A →ₐ[R] B) = torsionIdeal R B n := by
  rw [torsionIdeal, torsionIdeal, ← ideal_map_comp, ← nsmulAlgHom_comp_bialgHom φ n, ideal_map_comp,
    map_augIdeal_eq_of_surjective φ hφ]

private theorem ker_eq_map_ker_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (g : B →ₐ[R] C) :
    RingHom.ker g = (RingHom.ker (g.comp f)).map f := by
  rw [RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot,
    show Ideal.comap (g.comp f) ⊥ = Ideal.comap f (Ideal.comap g (⊥ : Ideal C)) from rfl,
    Ideal.map_comap_of_surjective _ hf]

private theorem isLocalRing_quotient_of_ker_eq [Algebra R A] [Algebra R B] [IsLocalRing B]
    (ρ : A →ₐ[R] B) (hρ : Function.Surjective ρ) {I : Ideal A} (hk : RingHom.ker ρ = I) :
    IsLocalRing (A ⧸ I) := by
  let E : B ≃ₐ[R] A ⧸ I :=
    (Ideal.quotientKerAlgEquivOfSurjective hρ).symm.trans (Ideal.quotientEquivAlgOfEq R hk)
  haveI : Nontrivial (A ⧸ I) := E.injective.nontrivial
  exact IsLocalRing.of_surjective' (E : B →+* A ⧸ I) E.surjective

end Ideals

section LevelStep

variable {R : Type*} [CommRing R] [Nontrivial R]
  {A₁ A₀ B₁ B₀ : Type*} [CommRing A₁] [CommRing A₀] [CommRing B₁] [CommRing B₀]
  [Bialgebra R A₁] [Bialgebra R A₀] [Bialgebra R B₁] [Bialgebra R B₀]

private theorem exists_bialgHom_connectedComponent_step
    (t : A₁ →ₐc[R] A₀) (ht : Function.Surjective t) (n : ℕ)
    (hkt : RingHom.ker t = torsionIdeal R A₁ n)
    (ρ₁ : A₁ →ₐc[R] B₁) (e₁ : A₁) (he₁ : IsIdempotentElem e₁)
    (hε₁ : Coalgebra.counit (R := R) e₁ = 1) (hρ₁ : Function.Surjective ρ₁)
    (hk₁ : RingHom.ker (ρ₁ : A₁ →ₐ[R] B₁) = Ideal.span {1 - e₁}) (hB₁ : IsLocalRing B₁)
    (ρ₀ : A₀ →ₐc[R] B₀) (e₀ : A₀) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := R) e₀ = 1) (hρ₀ : Function.Surjective ρ₀)
    (hk₀ : RingHom.ker (ρ₀ : A₀ →ₐ[R] B₀) = Ideal.span {1 - e₀}) (hB₀ : IsLocalRing B₀) :
    ∃ t₀ : B₁ →ₐc[R] B₀, t₀.comp ρ₁ = ρ₀.comp t ∧ Function.Surjective t₀ ∧ t e₁ = e₀ ∧
      RingHom.ker t₀ = torsionIdeal R B₁ n := by
  haveI := hB₀
  haveI := hB₁

  have h1 : ρ₀ (t e₁) = 1 := by
    have := apply_eq_one_of_isIdempotentElem ((ρ₀ : A₀ →+* B₀).comp (t : A₁ →+* A₀)) he₁
      (Bialgebra.counitAlgHom R B₀ : B₀ →+* R) ?_
    · exact this
    · change Coalgebra.counit (R := R) (ρ₀ (t e₁)) = 1
      rw [CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, hε₁]

  have hker : RingHom.ker (ρ₁ : A₁ →ₐ[R] B₁) ≤ RingHom.ker ((ρ₀.comp t : A₁ →ₐc[R] B₀) : A₁ →ₐ[R] B₀) := by
    rw [hk₁, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change ρ₀ (t (1 - e₁)) = 0
    rw [map_sub, map_one, map_sub, map_one, h1, sub_self]
  obtain ⟨t₀, ht₀⟩ := exists_bialgHom_comp_eq ρ₁ hρ₁ (ρ₀.comp t) hker
  have ht₀' : ∀ a, t₀ (ρ₁ a) = ρ₀ (t a) := fun a => DFunLike.congr_fun ht₀ a

  have hsurj : Function.Surjective t₀ := by
    intro b
    obtain ⟨a₀, rfl⟩ := hρ₀ b
    obtain ⟨a₁, rfl⟩ := ht a₀
    exact ⟨ρ₁ a₁, ht₀' a₁⟩

  have he' : IsIdempotentElem (t e₁) := he₁.map t
  have hε' : Coalgebra.counit (R := R) (t e₁) = 1 := by rw [CoalgHomClass.counit_comp_apply, hε₁]
  have hloc' : IsLocalRing (A₀ ⧸ Ideal.span {1 - t e₁}) := by

    have hle : RingHom.ker (ρ₁ : A₁ →ₐ[R] B₁) ≤
        RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {1 - t e₁})).comp (t : A₁ →ₐ[R] A₀)) := by
      rw [hk₁, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (t : A₁ →ₐ[R] A₀) (1 - e₁) = 1 - t e₁ := by rw [map_sub, map_one]; rfl
      rw [this]
      exact Ideal.mem_span_singleton_self _
    let σ : B₁ →ₐ[R] A₀ ⧸ Ideal.span {1 - t e₁} :=
      AlgHom.liftOfSurjective (ρ₁ : A₁ →ₐ[R] B₁) hρ₁ _ hle
    have hσ : Function.Surjective σ := by
      intro q
      obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ q
      obtain ⟨a₁, rfl⟩ := ht a₀
      refine ⟨ρ₁ a₁, ?_⟩
      exact DFunLike.congr_fun (AlgHom.liftOfSurjective_comp (ρ₁ : A₁ →ₐ[R] B₁) hρ₁ _ hle) a₁

    haveI : Nontrivial (A₀ ⧸ Ideal.span {1 - t e₁}) := by
      refine ⟨⟨0, 1, Ideal.Quotient.zero_ne_one_iff.2 fun htop => ?_⟩⟩
      have h1mem : (1 : A₀) ∈ Ideal.span {1 - t e₁} := by rw [htop]; exact Submodule.mem_top
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1mem
      have h := congrArg (Bialgebra.counitAlgHom R A₀) ha
      rw [map_mul, map_sub, map_one] at h
      change Coalgebra.counit (R := R) a * (1 - Coalgebra.counit (R := R) (t e₁)) = 1 at h
      rw [hε', sub_self, mul_zero] at h
      exact zero_ne_one h
    exact IsLocalRing.of_surjective' (σ : B₁ →+* _) hσ
  have hρ₀' : Function.Surjective (ρ₀ : A₀ →ₐ[R] B₀) := hρ₀
  have hρ₁' : Function.Surjective (ρ₁ : A₁ →ₐ[R] B₁) := hρ₁
  have heq : t e₁ = e₀ :=
    isIdempotentElem_unique (Bialgebra.counitAlgHom R A₀ : A₀ →+* R) he' he₀ hε' hε₀ hloc'
      (isLocalRing_quotient_of_ker_eq (ρ₀ : A₀ →ₐ[R] B₀) hρ₀' hk₀)
  refine ⟨t₀, ht₀, hsurj, heq, ?_⟩

  have hcomp : (t₀ : B₁ →ₐ[R] B₀).comp (ρ₁ : A₁ →ₐ[R] B₁) = (ρ₀ : A₀ →ₐ[R] B₀).comp (t : A₁ →ₐ[R] A₀) :=
    AlgHom.ext fun a => ht₀' a
  have hspan : Ideal.map (t : A₁ →ₐ[R] A₀) (Ideal.span {1 - e₁}) = Ideal.span {1 - e₀} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
    change Ideal.span {1 - t e₁} = _
    rw [heq]
  have ht' : Function.Surjective (t : A₁ →ₐ[R] A₀) := ht
  change RingHom.ker (t₀ : B₁ →ₐ[R] B₀) = torsionIdeal R B₁ n
  rw [ker_eq_map_ker_comp (ρ₁ : A₁ →ₐ[R] B₁) hρ₁' (t₀ : B₁ →ₐ[R] B₀), hcomp,
    show RingHom.ker ((ρ₀ : A₀ →ₐ[R] B₀).comp (t : A₁ →ₐ[R] A₀)) =
      Ideal.comap (t : A₁ →ₐ[R] A₀) (RingHom.ker (ρ₀ : A₀ →ₐ[R] B₀)) from
      (RingHom.comap_ker (ρ₀ : A₀ →+* B₀) (t : A₁ →+* A₀)).symm,
    hk₀, ← hspan, Ideal.comap_map_of_surjective _ ht', ← RingHom.ker_eq_comap_bot, Ideal.map_sup,
    (Ideal.map_eq_bot_iff_le_ker _).2 (le_of_eq hk₁.symm), bot_sup_eq]
  change Ideal.map (ρ₁ : A₁ →ₐ[R] B₁) (RingHom.ker t) = _
  rw [hkt, map_torsionIdeal_eq_of_surjective ρ₁ hρ₁ n]

end LevelStep

section Cocomm

variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

private theorem isCocomm_of_surjective [Coalgebra.IsCocomm R A] (ρ : A →ₐc[R] B)
    (hρ : Function.Surjective ρ) : Coalgebra.IsCocomm R B := by
  have hc := (ρ : A →ₗc[R] B).map_comp_comul
  have hsurj : Function.Surjective (ρ : A →ₗc[R] B).toLinearMap := hρ
  refine ⟨(LinearMap.cancel_right hsurj).1 ?_⟩
  rw [LinearMap.comp_assoc, ← hc, ← LinearMap.comp_assoc, ← TensorProduct.map_comp_comm_eq,
    LinearMap.comp_assoc, Coalgebra.IsCocomm.comm_comp_comul]

end Cocomm

section Finrank

variable {R : Type*} [CommRing R] [Nontrivial R]

private theorem finrank_eq_one_of_surjective {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Module.Free R N] [Module.Finite R N] [Nontrivial N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (hM : Module.finrank R M = 1) :
    Module.finrank R N = 1 := by
  have h1 : Module.finrank R N ≤ 1 := hM ▸ LinearMap.finrank_le_finrank_of_surjective hf
  have h2 : 0 < Module.finrank R N := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    by_contra h0
    have hE : IsEmpty (Module.Free.ChooseBasisIndex R N) :=
      Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 (not_lt.1 h0))
    exact not_subsingleton N (Module.Free.chooseBasis R N).repr.toEquiv.subsingleton
  omega

end Finrank

end PDivisibleGroup.ConnTower

open PDivisibleGroup.ConnTower in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) :
    ∃ (h₀ : ℕ) (_ : h₀ ≤ h)
      (R₀ : ℕ → Type v) (_ : ∀ v, CommRing (R₀ v)) (_ : ∀ v, HopfAlgebra 𝓞 (R₀ v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)) (_ : ∀ v, Module.Free 𝓞 (R₀ v))
      (_ : ∀ v, Module.Finite 𝓞 (R₀ v))
      (ρ : ∀ v, L v →ₐc[𝓞] R₀ v) (e : ∀ v, L v) (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v),
    (∀ v, Function.Surjective (t₀ v)) ∧
    (∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, (ρ v).comp (t v) = (t₀ v).comp (ρ (v + 1))) ∧
    ∀ v, IsIdempotentElem (e v) ∧ Coalgebra.counit (R := 𝓞) (e v) = 1 ∧
      Function.Surjective (ρ v) ∧ RingHom.ker (ρ v : L v →ₐ[𝓞] R₀ v) = Ideal.span {1 - e v} ∧
      IsLocalRing (R₀ v) ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) (R₀ v)) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (R₀ v))) := by
  classical

  have hksurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  haveI : Nontrivial 𝓞 := (algebraMap 𝓞 (ZMod p)).domain_nontrivial
  haveI : (Ideal.span {(p : 𝓞)}).IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective _ hksurj
  haveI : IsLocalRing 𝓞 := isLocalRing_of_isAdicComplete_maximal (Ideal.span {(p : 𝓞)})
  have hpp : p.Prime := Fact.out

  have hA := fun v => HopfAlgebra.exists_connectedComponent_of_isLocalRing_cartierDual_zmodp p hp hker
    (L v) (hunipL v)
  choose R₀ instCR instHA instFree instFin ρ e he hε hρ hk hloc hlock hunip₀ using hA
  haveI : ∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v) := fun v => isCocomm_of_surjective (ρ v) (hρ v)

  have hstep := fun v => exists_bialgHom_connectedComponent_step (t v) (ht v) (p ^ v) (hkerL v)
    (ρ (v + 1)) (e (v + 1)) (he _) (hε _) (hρ _) (hk _) (hloc _)
    (ρ v) (e v) (he v) (hε v) (hρ v) (hk v) (hloc v)
  choose t₀ ht₀c ht₀s hte ht₀k using hstep

  have hCRS := fun v =>
    PDivisibleGroup.finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub 𝓞 p h L t ht hrankL hkerL
      v (R₀ (v + 1)) (ρ (v + 1)) (e (v + 1)) (he _) (hε _) (hρ _) (hk _) (hloc _)
      (R₀ v) (ρ v) (e v) (he v) (hε v) (hρ v) (hk v) (hloc v)

  obtain ⟨T, -, -, hTsurj, hTker, -, -⟩ :=
    PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L t ht hrankL hkerL
  have hmid : ∀ v, Module.finrank 𝓞 (R₀ (v + 1) ⧸ torsionIdeal 𝓞 (R₀ (v + 1)) p) =
      Module.finrank 𝓞 (R₀ 1) := by
    intro v

    have key : ∀ N : ℕ, N = 1 + v → ∃ S : L N →ₐc[𝓞] L 1, Function.Surjective S ∧
        RingHom.ker S = torsionIdeal 𝓞 (L N) (p ^ 1) := by
      rintro N rfl
      exact ⟨T 1 v, hTsurj 1 v, hTker 1 v⟩
    obtain ⟨S, hS, hSk⟩ := key (v + 1) (Nat.add_comm v 1)
    obtain ⟨s₀, -, hs₀, -, hs₀k⟩ := exists_bialgHom_connectedComponent_step S hS (p ^ 1) hSk
      (ρ (v + 1)) (e (v + 1)) (he _) (hε _) (hρ _) (hk _) (hloc _)
      (ρ 1) (e 1) (he 1) (hε 1) (hρ 1) (hk 1) (hloc 1)
    rw [pow_one] at hs₀k
    have hs₀k' : RingHom.ker (s₀ : R₀ (v + 1) →ₐ[𝓞] R₀ 1) = torsionIdeal 𝓞 (R₀ (v + 1)) p := hs₀k
    have hs₀' : Function.Surjective (s₀ : R₀ (v + 1) →ₐ[𝓞] R₀ 1) := hs₀
    exact ((Ideal.quotientEquivAlgOfEq 𝓞 hs₀k'.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hs₀')).toLinearEquiv.finrank_eq

  have h0 : Module.finrank 𝓞 (R₀ 0) = 1 := by
    haveI := hloc 0
    have hρ' : Function.Surjective ((ρ 0 : L 0 →ₐ[𝓞] R₀ 0).toLinearMap) := hρ 0
    exact finrank_eq_one_of_surjective _ hρ' (by rw [hrankL 0, zero_mul, pow_zero])

  obtain ⟨h₀, hh₀, h1⟩ : ∃ h₀ ≤ h, Module.finrank 𝓞 (R₀ 1) = p ^ h₀ := by
    obtain ⟨-, _, _, hrank⟩ :=
      HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (ρ 1) (hρ 1)
    have hdvd : Module.finrank 𝓞 (R₀ 1) ∣ p ^ h := by
      refine ⟨Module.rankAtStalk (R := 𝓞) ↥(HopfAlgebra.hopfKer (ρ 1)) (IsLocalRing.closedPoint 𝓞), ?_⟩
      rw [mul_comm, hrank, hrankL 1, one_mul]
    exact (Nat.dvd_prime_pow hpp).1 hdvd

  have hrank : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀) := by
    intro v
    induction v with
    | zero => rw [h0, zero_mul, pow_zero]
    | succ v ih => rw [(hCRS v).2, hmid v, h1, ih, Nat.succ_mul, pow_add, mul_comm]

  exact ⟨h₀, hh₀, R₀, instCR, instHA, inferInstance, instFree, instFin, ρ, e, t₀, ht₀s, hrank, ht₀k,
    fun v => (ht₀c v).symm, fun v => ⟨he v, hε v, hρ v, hk v, hloc v, hlock v, hunip₀ v⟩⟩

end S_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual (solution)
