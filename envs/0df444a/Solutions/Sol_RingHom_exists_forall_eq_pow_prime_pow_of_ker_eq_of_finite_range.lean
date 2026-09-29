-- Prove2me | solution 1 for RingHom.exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2e668bce-e484-5cff-afc9-969cdc9a8a26

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range

set_option autoImplicit false

namespace AlignAux

theorem range_eq_rootSet {k L : Type} [Field k] [Fintype k] [Field L] (g : k →+* L) :
    Set.range g = {y : L | y ^ Fintype.card k = y} := by
  classical
  set q := Fintype.card k with hq

  have hsub : Set.range g ⊆ {y : L | y ^ q = y} := by
    rintro _ ⟨x, rfl⟩
    show g x ^ q = g x
    rw [← map_pow, FiniteField.pow_card]

  have hfinR : {y : L | y ^ q = y}.Finite := by
    have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial L) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
    refine (Polynomial.X ^ q - Polynomial.X : Polynomial L).rootSet_finite L |>.subset ?_
    intro y hy
    rw [Polynomial.mem_rootSet_of_ne hne]
    simp only [map_sub, map_pow, Polynomial.aeval_X]
    exact sub_eq_zero.mpr hy
  have hcardR : hfinR.toFinset.card ≤ q := by
    have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial L) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
    have h1 : hfinR.toFinset.card ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial L).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro y hy
      have hy' : y ∈ hfinR.toFinset := hy
      rw [Set.Finite.mem_toFinset] at hy'
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      exact sub_eq_zero.mpr hy'
    have h2 : (Polynomial.X ^ q - Polynomial.X : Polynomial L).natDegree = q :=
      FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card
    omega
  have hcardIm : (Finset.univ.image g).card = q := by
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ]
  have himsub : Finset.univ.image g ⊆ hfinR.toFinset := by
    intro y hy
    rw [Set.Finite.mem_toFinset]
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact hsub ⟨x, rfl⟩
  have heq : Finset.univ.image g = hfinR.toFinset :=
    Finset.eq_of_subset_of_card_le himsub (by rw [hcardIm]; exact hcardR)
  apply Set.Subset.antisymm hsub
  intro y hy
  have : y ∈ hfinR.toFinset := (Set.Finite.mem_toFinset _).mpr hy
  rw [← heq, Finset.mem_image] at this
  obtain ⟨x, -, rfl⟩ := this
  exact ⟨x, rfl⟩

theorem exists_pow_of_two_embeddings {k L : Type} [Field k] [Fintype k] [Field L] (p : ℕ) [Fact p.Prime] [CharP k p]
    (g₁ g₂ : k →+* L) : ∃ j : ℕ, ∀ x : k, g₂ x = g₁ x ^ p ^ j := by
  classical

  have hrange : Set.range g₂ = Set.range g₁ := by rw [range_eq_rootSet, range_eq_rootSet]

  let e₁ : k ≃+* g₁.range := RingEquiv.ofBijective g₁.rangeRestrict
    ⟨fun x y h => g₁.injective (congrArg Subtype.val h), g₁.rangeRestrict_surjective⟩
  have hmem : ∀ x, g₂ x ∈ g₁.range := fun x => by
    have : g₂ x ∈ Set.range g₁ := hrange ▸ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  let g₂' : k →+* g₁.range := g₂.codRestrict g₁.range hmem
  let τ : k →+* k := e₁.symm.toRingHom.comp g₂'
  have hτ : ∀ x, g₁ (τ x) = g₂ x := by
    intro x
    have h1 : (e₁ (e₁.symm (g₂' x)) : L) = g₂' x := by rw [RingEquiv.apply_symm_apply]
    exact h1

  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hcomm : ∀ a : ZMod p, τ (algebraMap (ZMod p) k a) = algebraMap (ZMod p) k a := fun a =>
    RingHom.congr_fun (Subsingleton.elim (τ.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)) a
  let τa : k →ₐ[ZMod p] k := { toRingHom := τ, commutes' := hcomm }
  obtain ⟨⟨n, hn⟩, hτn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) k).2 τa
  refine ⟨n, fun x => ?_⟩
  have hx : τ x = x ^ p ^ n := by
    have := congrArg (fun f : k →ₐ[ZMod p] k => f x) hτn
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at this
    exact this.symm
  rw [← hτ, hx, map_pow]

end AlignAux

theorem solution
    {T L : Type} [CommRing T] [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (f₁ f₂ : T →+* L) (hker : RingHom.ker f₁ = RingHom.ker f₂)
    (hfin : (Set.range f₁).Finite) :
    ∃ j : ℕ, ∀ t : T, f₂ t = f₁ t ^ p ^ j := by
  classical

  set I := RingHom.ker f₁ with hI
  haveI : I.IsPrime := RingHom.ker_isPrime f₁
  haveI : IsDomain (T ⧸ I) := Ideal.Quotient.isDomain I

  haveI : _root_.Finite (T ⧸ I) := by
    have e := RingHom.quotientKerEquivRange f₁
    haveI : _root_.Finite f₁.range := by
      have : (f₁.range : Set L).Finite := by rw [RingHom.coe_range]; exact hfin
      exact this.to_subtype
    exact _root_.Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype (T ⧸ I) := Fintype.ofFinite _
  haveI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I (Finite.isDomain_to_isField (T ⧸ I))
  letI : Field (T ⧸ I) := Ideal.Quotient.field I

  let g₁ : T ⧸ I →+* L := Ideal.Quotient.lift I f₁ (fun a ha => ha)
  let g₂ : T ⧸ I →+* L := Ideal.Quotient.lift I f₂ (fun a ha => by
    have : a ∈ RingHom.ker f₂ := hker ▸ ha
    exact this)
  haveI : CharP (T ⧸ I) p := (RingHom.charP_iff_charP g₁ p).mpr inferInstance
  obtain ⟨j, hj⟩ := AlignAux.exists_pow_of_two_embeddings p g₁ g₂
  refine ⟨j, fun t => ?_⟩
  have h1 : f₁ t = g₁ (Ideal.Quotient.mk I t) := (Ideal.Quotient.lift_mk I f₁ _).symm
  have h2 : f₂ t = g₂ (Ideal.Quotient.mk I t) := (Ideal.Quotient.lift_mk I f₂ _).symm
  rw [h1, h2, hj]

end S_RingHom_exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range
end P2MW
export P2MW.S_RingHom_exists_forall_eq_pow_prime_pow_of_ker_eq_of_finite_range (solution)
