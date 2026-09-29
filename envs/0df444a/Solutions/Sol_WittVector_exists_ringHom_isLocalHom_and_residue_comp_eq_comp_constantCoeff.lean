-- Prove2me | solution 1 for WittVector.exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9d9a0388-742a-5863-bed6-2befb0be981b

import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.Teichmuller
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff

set_option autoImplicit false

namespace W3Cohen

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]
variable {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ p]
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem charP_residueField (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) :
    CharP (ResidueField 𝒪) p := by
  have h0 : ((p : ℕ) : ResidueField 𝒪) = 0 := by
    have h : residue 𝒪 (p : 𝒪) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp𝒪
    simp only [map_natCast] at h
    exact h
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

section Teich

variable (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (f : k₀ →+* ResidueField 𝒪)

include hp𝒪 in

theorem existsUnique_teich (a : k₀) :
    ∃! x : 𝒪, x ^ Nat.card k₀ = x ∧ residue 𝒪 x = f a := by
  haveI := Fintype.ofFinite k₀
  haveI hkchar : CharP (ResidueField 𝒪) p := charP_residueField hp𝒪
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card k₀ p
  set q := Nat.card k₀ with hqdef
  have hqfin : q = Fintype.card k₀ := Nat.card_eq_fintype_card
  have hq1 : 1 < q := by rw [hqfin]; exact Fintype.one_lt_card
  have hqres : ((q : ℕ) : ResidueField 𝒪) = 0 := by
    rw [hqfin, hcard]; push_cast
    rw [CharP.cast_eq_zero (ResidueField 𝒪) p]
    exact zero_pow n.pos.ne'
  have hfq : ∀ β : k₀, (f β) ^ q = f β := fun β => by
    rw [← map_pow, hqfin, FiniteField.pow_card]

  set F : 𝒪[X] := X ^ q - X with hF
  have hFmonic : F.Monic :=
    Polynomial.monic_X_pow_sub (degree_X.trans_lt (by exact_mod_cast hq1))
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal 𝒪) (f a)
  have hres_a₀ : residue 𝒪 a₀ = f a := ha₀
  have heval : F.eval a₀ ∈ maximalIdeal 𝒪 := by
    have h : residue 𝒪 (F.eval a₀) = 0 := by
      have he : F.eval a₀ = a₀ ^ q - a₀ := by simp [hF]
      rw [he, map_sub, map_pow, hres_a₀, hfq, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal 𝒪) (F.derivative.eval a₀)) := by
    have hd : residue 𝒪 (F.derivative.eval a₀) = -1 := by
      have hdf : F.derivative = C (q : 𝒪) * X ^ (q - 1) - 1 := by
        simp [hF, Polynomial.derivative_X_pow]
      rw [hdf]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
      have hqz : residue 𝒪 ((q : ℕ) : 𝒪) = 0 := by
        rw [map_natCast, hqres]
      rw [map_sub, map_mul, hqz, zero_mul, map_one, zero_sub]
    show IsUnit (residue 𝒪 (F.derivative.eval a₀))
    rw [hd]
    exact isUnit_one.neg
  obtain ⟨x, hxroot, hxsub⟩ :=
    HenselianRing.is_henselian (I := maximalIdeal 𝒪) F hFmonic a₀ heval hderiv
  have hxq : x ^ q = x := by
    have h := hxroot
    simp only [Polynomial.IsRoot, hF, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X] at h
    exact sub_eq_zero.mp h
  have hxres : residue 𝒪 x = f a := by
    have h : residue 𝒪 (x - a₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxsub
    rw [map_sub, sub_eq_zero] at h
    rw [h, hres_a₀]
  refine ⟨x, ⟨hxq, hxres⟩, ?_⟩

  rintro y ⟨hyq, hyres⟩
  have hsum_mem : (∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) ∈ maximalIdeal 𝒪 := by
    have h : residue 𝒪 (∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) = 0 := by
      rw [map_sum]
      have hterm : ∀ i ∈ Finset.range q,
          residue 𝒪 (y ^ i * x ^ (q - 1 - i)) = (f a) ^ (q - 1) := by
        intro i hi
        rw [map_mul, map_pow, map_pow, hyres, hxres, ← pow_add]
        congr 1
        have := Finset.mem_range.mp hi
        omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show ((q : ℕ) : ResidueField 𝒪) = 0 from hqres, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  have hunit : IsUnit ((∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) - 1) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) - 1 ∈ maximalIdeal 𝒪 := hnu
    have h1 : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
      have h := Ideal.sub_mem (maximalIdeal 𝒪) hsum_mem hmem
      simp only [sub_sub_cancel] at h
      exact h
    exact (maximalIdeal.isMaximal 𝒪).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hgeom : (∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) * (y - x) = y ^ q - x ^ q :=
    geom_sum₂_mul y x q
  have hzero : (y - x) * ((∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) - 1) = 0 := by
    have h : (y - x) * (∑ i ∈ Finset.range q, y ^ i * x ^ (q - 1 - i)) = y - x := by
      rw [mul_comm, hgeom, hyq, hxq]
    rw [mul_sub, h, mul_one, sub_self]
  have := hunit.ne_zero
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h this

noncomputable def teich (a : k₀) : 𝒪 :=
  (existsUnique_teich hp𝒪 f a).exists.choose

theorem teich_pow (a : k₀) : teich hp𝒪 f a ^ Nat.card k₀ = teich hp𝒪 f a :=
  (existsUnique_teich hp𝒪 f a).exists.choose_spec.1

theorem residue_teich (a : k₀) : residue 𝒪 (teich hp𝒪 f a) = f a :=
  (existsUnique_teich hp𝒪 f a).exists.choose_spec.2

theorem eq_teich {a : k₀} {x : 𝒪} (hx : x ^ Nat.card k₀ = x) (hres : residue 𝒪 x = f a) :
    x = teich hp𝒪 f a :=
  (existsUnique_teich hp𝒪 f a).unique ⟨hx, hres⟩
    ⟨teich_pow hp𝒪 f a, residue_teich hp𝒪 f a⟩

theorem teich_one : teich hp𝒪 f 1 = 1 :=
  (eq_teich hp𝒪 f (one_pow _) (by rw [map_one, map_one])).symm

theorem teich_zero : teich hp𝒪 f 0 = 0 :=
  (eq_teich hp𝒪 f (zero_pow (by
    have : 1 < Nat.card k₀ := by
      haveI := Fintype.ofFinite k₀
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega)) (by rw [map_zero, map_zero])).symm

theorem teich_mul (a b : k₀) :
    teich hp𝒪 f (a * b) = teich hp𝒪 f a * teich hp𝒪 f b :=
  ((eq_teich hp𝒪 f (by rw [mul_pow, teich_pow, teich_pow])
    (by rw [map_mul, residue_teich, residue_teich, map_mul]))).symm

section CharPLeg

variable [CharP 𝒪 p]

include hp𝒪 in
theorem teich_add (a b : k₀) :
    teich hp𝒪 f (a + b) = teich hp𝒪 f a + teich hp𝒪 f b := by
  haveI := Fintype.ofFinite k₀
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card k₀ p
  refine ((eq_teich hp𝒪 f ?_ ?_)).symm
  · rw [show Nat.card k₀ = p ^ (n : ℕ) by rw [Nat.card_eq_fintype_card, hcard],
      add_pow_char_pow,
      show (p : ℕ) ^ (n : ℕ) = Nat.card k₀ by rw [Nat.card_eq_fintype_card, hcard],
      teich_pow, teich_pow]
  · rw [map_add, map_add, residue_teich, residue_teich]

noncomputable def teichHom : k₀ →+* 𝒪 where
  toFun := teich hp𝒪 f
  map_one' := teich_one hp𝒪 f
  map_mul' := teich_mul hp𝒪 f
  map_zero' := teich_zero hp𝒪 f
  map_add' := teich_add hp𝒪 f

include hp𝒪 in

theorem cohen_of_charP :
    ∃ g : WittVector p k₀ →+* 𝒪, IsLocalHom g ∧
      (residue 𝒪).comp g = f.comp (WittVector.constantCoeff : WittVector p k₀ →+* k₀) := by
  refine ⟨(teichHom hp𝒪 f).comp WittVector.constantCoeff, ?_, ?_⟩
  · constructor
    intro x hx
    have hfcc : f (WittVector.constantCoeff x) ≠ 0 := by
      rw [← residue_teich hp𝒪 f (WittVector.constantCoeff x)]
      intro h0
      exact (maximalIdeal.isMaximal 𝒪).ne_top
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) hx)
    have hcc : x.coeff 0 ≠ 0 := fun h0 => hfcc (by
      rw [show WittVector.constantCoeff x = x.coeff 0 from rfl, h0, map_zero])
    exact WittVector.isUnit_of_coeff_zero_ne_zero x hcc
  · ext x
    simp only [RingHom.comp_apply]
    exact residue_teich hp𝒪 f _

end CharPLeg

section CharZeroLeg

open WittVector

omit [Finite k₀] [CharP k₀ p] in

theorem teichmuller_injective :
    Function.Injective (WittVector.teichmuller p : k₀ →* WittVector p k₀) := by
  intro a b h
  have := congrArg (fun w : WittVector p k₀ => w.coeff 0) h
  simpa [WittVector.teichmuller_coeff_zero] using this

variable {c : k₀ˣ} (hc : ∀ a : k₀ˣ, a ∈ Subgroup.zpowers c)

include hc in

theorem isPrimitiveRoot_gen : IsPrimitiveRoot (c : k₀) (Nat.card k₀ - 1) := by
  haveI := Fintype.ofFinite k₀
  haveI : DecidableEq k₀ := Classical.decEq k₀
  have horder : orderOf c = Nat.card k₀ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc]
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]
  have h := IsPrimitiveRoot.orderOf (c : k₀)
  rw [orderOf_units, horder] at h
  exact h

omit [CharP k₀ p] in
include hc in
theorem isPrimitiveRoot_wittTeich :
    IsPrimitiveRoot (WittVector.teichmuller p (c : k₀)) (Nat.card k₀ - 1) := by
  have hk := isPrimitiveRoot_gen hc
  constructor
  · rw [← MonoidHom.map_pow, hk.pow_eq_one, MonoidHom.map_one]
  · intro l hl
    apply hk.dvd_of_pow_eq_one
    apply teichmuller_injective (p := p)
    rw [MonoidHom.map_pow, hl, MonoidHom.map_one]

include hp𝒪 hc in
theorem isPrimitiveRoot_teich :
    IsPrimitiveRoot (teich hp𝒪 f (c : k₀)) (Nat.card k₀ - 1) := by
  have hk := isPrimitiveRoot_gen hc
  have hq1 : 1 < Nat.card k₀ := by
    haveI := Fintype.ofFinite k₀
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hv : teich hp𝒪 f (c : k₀) ^ (Nat.card k₀ - 1) = 1 := by
    have hvq := teich_pow hp𝒪 f (c : k₀)
    have hvne : teich hp𝒪 f (c : k₀) ≠ 0 := by
      intro h0
      have hres := residue_teich hp𝒪 f (c : k₀)
      rw [h0, map_zero] at hres
      exact Units.ne_zero c (f.injective (hres.symm.trans (map_zero f).symm))
    have hstep : teich hp𝒪 f (c : k₀) *
        (teich hp𝒪 f (c : k₀) ^ (Nat.card k₀ - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ',
        show Nat.card k₀ - 1 + 1 = Nat.card k₀ by omega, hvq, sub_self]
    rcases mul_eq_zero.mp hstep with h | h
    · exact absurd h hvne
    · exact sub_eq_zero.mp h
  refine ⟨hv, ?_⟩
  intro l hl
  apply hk.dvd_of_pow_eq_one
  have hres := congrArg (residue 𝒪) hl
  rw [map_pow, residue_teich, map_one, ← map_pow, ← map_one f] at hres
  exact f.injective hres

omit [CharP k₀ p] in
include hc in
theorem evalW_F_eq_zero :
    (Polynomial.X ^ (Nat.card k₀ - 1) - 1 : Polynomial ℤ).eval₂
      (Int.castRingHom (WittVector p k₀)) (WittVector.teichmuller p (c : k₀)) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one,
    (isPrimitiveRoot_wittTeich hc).pow_eq_one, sub_self]

include hp𝒪 hc in
theorem evalO_F_eq_zero :
    (Polynomial.X ^ (Nat.card k₀ - 1) - 1 : Polynomial ℤ).eval₂
      (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀)) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one,
    (isPrimitiveRoot_teich hp𝒪 f hc).pow_eq_one, sub_self]

omit [Finite k₀] [CharP k₀ p] in
theorem constantCoeff_evalW (Q : Polynomial ℤ) :
    WittVector.constantCoeff (Q.eval₂ (Int.castRingHom (WittVector p k₀))
      (WittVector.teichmuller p (c : k₀))) = Q.eval₂ (Int.castRingHom k₀) (c : k₀) := by
  have h1 : (WittVector.constantCoeff).comp (Int.castRingHom (WittVector p k₀)) =
      Int.castRingHom k₀ := RingHom.ext_int _ _
  rw [Polynomial.hom_eval₂, h1]
  congr 1

omit [Finite k₀] in
theorem evalk_eq_zero_of_dvd (Q : Polynomial ℤ)
    (h : ((p : ℕ) : WittVector p k₀) ∣ Q.eval₂ (Int.castRingHom (WittVector p k₀))
      (WittVector.teichmuller p (c : k₀))) :
    Q.eval₂ (Int.castRingHom k₀) (c : k₀) = 0 := by
  obtain ⟨w, hw⟩ := h
  have hcc := congrArg WittVector.constantCoeff hw
  rw [constantCoeff_evalW, map_mul, map_natCast, CharP.cast_eq_zero k₀ p, zero_mul] at hcc
  exact hcc

include hp𝒪 in
theorem residue_evalO (Q : Polynomial ℤ) :
    IsLocalRing.residue 𝒪 (Q.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀))) =
      f (Q.eval₂ (Int.castRingHom k₀) (c : k₀)) := by
  have h1 : (IsLocalRing.residue 𝒪).comp (Int.castRingHom 𝒪) =
      f.comp (Int.castRingHom k₀) := RingHom.ext_int _ _
  rw [Polynomial.hom_eval₂, h1, residue_teich hp𝒪 f]
  exact (Polynomial.hom_eval₂ _ _ _ _).symm

include hp𝒪 in
theorem isUnit_evalO (Q : Polynomial ℤ)
    (h : Q.eval₂ (Int.castRingHom k₀) (c : k₀) ≠ 0) :
    IsUnit (Q.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀))) := by
  by_contra hnu
  have hmem := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have h0 : IsLocalRing.residue 𝒪
      (Q.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [residue_evalO hp𝒪 f] at h0
  exact h (f.injective (by rw [h0, map_zero]))

include hc in

theorem exists_clearing (Q : Polynomial ℤ)
    (hQ : Q.eval₂ (Int.castRingHom k₀) (c : k₀) = 0) :
    ∃ T D B : Polynomial ℤ,
      T.eval₂ (Int.castRingHom k₀) (c : k₀) ≠ 0 ∧
      T * Q = (Polynomial.X ^ (Nat.card k₀ - 1) - 1) * D +
        Polynomial.C ((p : ℕ) : ℤ) * B := by
  letI : Algebra (ZMod p) k₀ := (ZMod.castHom dvd_rfl k₀).toAlgebra
  haveI : Module.Finite (ZMod p) k₀ := Module.Finite.of_finite
  have hplumb : ∀ P : Polynomial ℤ,
      Polynomial.aeval (c : k₀) (P.map (Int.castRingHom (ZMod p))) =
        P.eval₂ (Int.castRingHom k₀) (c : k₀) := by
    intro P
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap (ZMod p) k₀).comp (Int.castRingHom (ZMod p)) =
        Int.castRingHom k₀ from RingHom.ext_int _ _]
  have hqp : ((Nat.card k₀ - 1 : ℕ) : ZMod p) ≠ 0 := by
    haveI := Fintype.ofFinite k₀
    have hq1 : 1 < Nat.card k₀ := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    obtain ⟨m, hpp, hcard⟩ := FiniteField.card k₀ p
    have hq0 : ((Nat.card k₀ : ℕ) : ZMod p) = 0 := by
      rw [Nat.card_eq_fintype_card, hcard]
      push_cast
      rw [ZMod.natCast_self, zero_pow m.pos.ne']
    rw [Nat.cast_sub (by omega), hq0, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  have hFsf : Squarefree (Polynomial.X ^ (Nat.card k₀ - 1) - 1 : Polynomial (ZMod p)) := by
    have hsep := Polynomial.separable_X_pow_sub_C (1 : ZMod p) hqp one_ne_zero
    rw [Polynomial.C_1] at hsep
    exact hsep.squarefree
  have hint : IsIntegral (ZMod p) (c : k₀) := IsIntegral.of_finite _ _
  have hg1F : minpoly (ZMod p) (c : k₀) ∣
      (Polynomial.X ^ (Nat.card k₀ - 1) - 1 : Polynomial (ZMod p)) := by
    refine minpoly.dvd _ _ ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one,
      (isPrimitiveRoot_gen hc).pow_eq_one, sub_self]
  obtain ⟨Tbar, hTbar⟩ := hg1F
  have hg1T : ¬ minpoly (ZMod p) (c : k₀) ∣ Tbar := by
    rintro ⟨E, hE⟩
    exact (minpoly.irreducible hint).not_isUnit
      (hFsf (minpoly (ZMod p) (c : k₀)) ⟨E, by rw [hTbar, hE]; ring⟩)
  have hQbar : minpoly (ZMod p) (c : k₀) ∣ Q.map (Int.castRingHom (ZMod p)) := by
    refine minpoly.dvd _ _ ?_
    rw [hplumb, hQ]
  obtain ⟨D0, hD0⟩ := hQbar
  obtain ⟨T, hT⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    ZMod.intCast_surjective Tbar
  obtain ⟨D, hD⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    ZMod.intCast_surjective D0
  have hker : (T * Q - (Polynomial.X ^ (Nat.card k₀ - 1) - 1) * D).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hT, hD,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      hD0, hTbar]
    ring
  have hCp : Polynomial.C ((p : ℕ) : ℤ) ∣
      T * Q - (Polynomial.X ^ (Nat.card k₀ - 1) - 1) * D := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hco := congrArg (fun P => Polynomial.coeff P i) hker
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hco
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hco
  obtain ⟨B, hB⟩ := hCp
  refine ⟨T, D, B, ?_, by rw [← hB]; ring⟩
  intro h0
  refine hg1T (minpoly.dvd _ _ ?_)
  rw [← hT, hplumb]
  exact h0

include hp𝒪 hc in

theorem pow_dvd_evalO_of_pow_dvd_evalW :
    ∀ (n : ℕ) (Q : Polynomial ℤ),
      ((p : ℕ) : WittVector p k₀) ^ n ∣ Q.eval₂ (Int.castRingHom (WittVector p k₀))
        (WittVector.teichmuller p (c : k₀)) →
      ((p : ℕ) : 𝒪) ^ n ∣ Q.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀)) := by
  intro n
  induction n with
  | zero => intro Q _; rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    intro Q hQ
    have hpne : ((p : ℕ) : WittVector p k₀) ≠ 0 :=
      Irreducible.ne_zero (WittVector.irreducible p)
    have hp1 := (dvd_pow_self ((p : ℕ) : WittVector p k₀) (Nat.succ_ne_zero n)).trans hQ
    have hc0 := evalk_eq_zero_of_dvd Q hp1
    obtain ⟨T, D, B, hT0, hTQ⟩ := exists_clearing hc Q hc0
    have hu := congrArg (Polynomial.eval₂ (Int.castRingHom (WittVector p k₀))
      (WittVector.teichmuller p (c : k₀))) hTQ
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Int.coe_castRingHom, Int.cast_natCast] at hu
    rw [evalW_F_eq_zero hc, zero_mul, zero_add] at hu
    have hdvdB : ((p : ℕ) : WittVector p k₀) ^ n ∣
        B.eval₂ (Int.castRingHom (WittVector p k₀)) (WittVector.teichmuller p (c : k₀)) := by
      have h1 := hu ▸ hQ.mul_left (T.eval₂ (Int.castRingHom (WittVector p k₀))
        (WittVector.teichmuller p (c : k₀)))
      rw [pow_succ'] at h1
      exact (mul_dvd_mul_iff_left hpne).mp h1
    have hBv := ih B hdvdB
    have hv := congrArg (Polynomial.eval₂ (Int.castRingHom 𝒪)
      (teich hp𝒪 f (c : k₀))) hTQ
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Int.coe_castRingHom, Int.cast_natCast] at hv
    rw [evalO_F_eq_zero hp𝒪 f hc, zero_mul, zero_add] at hv
    have h2 : ((p : ℕ) : 𝒪) ^ (n + 1) ∣
        T.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀)) *
        Q.eval₂ (Int.castRingHom 𝒪) (teich hp𝒪 f (c : k₀)) := by
      rw [hv, pow_succ']
      exact mul_dvd_mul_left _ hBv
    exact ((isUnit_evalO hp𝒪 f T hT0).dvd_mul_left).mp h2

end CharZeroLeg

end Teich

open IsLocalRing Polynomial WittVector

variable {p : ℕ} [Fact p.Prime]
variable {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ p]

section Density

omit [Finite k₀] in

theorem ker_constantCoeff_eq_span [PerfectRing k₀ p] :
    RingHom.ker (constantCoeff : WittVector p k₀ →+* k₀) =
      Ideal.span {(p : WittVector p k₀)} := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    · obtain ⟨m, b, hb⟩ := exists_eq_pow_p_mul' x hx0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exfalso
        have hu : IsUnit (constantCoeff (x : WittVector p k₀)) := by
          refine IsUnit.map _ ?_
          rw [hb, pow_zero, one_mul]
          exact b.isUnit
        rw [hx] at hu
        exact hu.ne_zero rfl
      · rw [hb]
        exact (dvd_pow_self ((p : ℕ) : WittVector p k₀) hm.ne').mul_right _
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

omit [Finite k₀] in

theorem maximalIdeal_wittVector_eq_span [PerfectRing k₀ p] :
    maximalIdeal (WittVector p k₀) = Ideal.span {(p : WittVector p k₀)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p)

theorem exists_pow_eq {c : k₀ˣ} (hc : ∀ a : k₀ˣ, a ∈ Subgroup.zpowers c) {a : k₀} (ha : a ≠ 0) :
    ∃ k : ℕ, (c : k₀) ^ k = a := by
  haveI : Finite k₀ˣ := Finite.of_injective (Units.val) Units.val_injective
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc (Units.mk0 a ha))
  have hopos : 0 < orderOf c := (isOfFinOrder_of_finite c).orderOf_pos
  have hnn : 0 ≤ m % (orderOf c : ℤ) :=
    Int.emod_nonneg m (Int.natCast_ne_zero.mpr hopos.ne')
  refine ⟨(m % (orderOf c : ℤ)).toNat, ?_⟩
  have hkunit : c ^ (m % (orderOf c : ℤ)).toNat = Units.mk0 a ha := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf, hm]
  calc (c : k₀) ^ (m % (orderOf c : ℤ)).toNat
      = ((c ^ (m % (orderOf c : ℤ)).toNat : k₀ˣ) : k₀) := (Units.val_pow_eq_pow_val c _).symm
    _ = a := by rw [hkunit, Units.val_mk0]

theorem density_teichmuller {c : k₀ˣ} (hc : ∀ a : k₀ˣ, a ∈ Subgroup.zpowers c)
    (x : WittVector p k₀) (n : ℕ) :
    ∃ Q : ℤ[X], x - Q.eval₂ (Int.castRingHom _) (teichmuller p (c : k₀)) ∈
      Ideal.span {(p : WittVector p k₀)} ^ n := by
  haveI : PerfectRing k₀ p := PerfectRing.ofFiniteOfIsReduced p k₀
  set u := teichmuller p (c : k₀)
  have hccu : constantCoeff u = (c : k₀) := teichmuller_coeff_zero p (c : k₀)
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hQ
    obtain ⟨y, hy⟩ := hQ

    rcases eq_or_ne (constantCoeff y) 0 with hcc | hcc
    ·
      refine ⟨Q, ?_⟩
      obtain ⟨z, hz⟩ : (p : WittVector p k₀) ∣ y := by
        rw [← Ideal.mem_span_singleton, ← ker_constantCoeff_eq_span]
        exact hcc
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton', ← hy, hz]
      exact ⟨z, by rw [mul_right_comm, ← pow_succ', mul_comm]⟩
    · obtain ⟨k, hk⟩ := exists_pow_eq hc hcc

      obtain ⟨z, hz⟩ : (p : WittVector p k₀) ∣ (y - u ^ k) := by
        rw [← Ideal.mem_span_singleton, ← ker_constantCoeff_eq_span]
        show constantCoeff (y - u ^ k) = 0
        rw [map_sub, map_pow, hccu, hk, sub_self]
      refine ⟨Q + C ((p : ℤ) ^ n) * X ^ k, ?_⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      have heval : ((Q + C ((p : ℤ) ^ n) * X ^ k).eval₂ (Int.castRingHom _) u : WittVector p k₀)
          = Q.eval₂ (Int.castRingHom _) u + (p : WittVector p k₀) ^ n * u ^ k := by
        rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow, map_natCast]
      refine ⟨z, ?_⟩
      rw [heval, sub_add_eq_sub_sub, ← hy, mul_comm y, ← mul_sub, hz, ← mul_assoc, ← pow_succ,
        mul_comm]

end Density

section Limit

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

structure CohenData (f : k₀ →+* ResidueField 𝒪) where
  p_mem : (p : 𝒪) ∈ maximalIdeal 𝒪
  u : WittVector p k₀
  v : 𝒪
  hvres : residue 𝒪 v = f (constantCoeff u)
  key : ∀ (Q : ℤ[X]) (n : ℕ),
    Q.eval₂ (Int.castRingHom _) u ∈ Ideal.span {(p : WittVector p k₀)} ^ n →
    Q.eval₂ (Int.castRingHom _) v ∈ Ideal.span {(p : 𝒪)} ^ n
  density : ∀ (x : WittVector p k₀) (n : ℕ), ∃ Q : ℤ[X],
    x - Q.eval₂ (Int.castRingHom _) u ∈ Ideal.span {(p : WittVector p k₀)} ^ n

namespace CohenData

variable {f : k₀ →+* ResidueField 𝒪} (D : CohenData (p := p) f)

noncomputable def Q (x : WittVector p k₀) (n : ℕ) : ℤ[X] :=
  (D.density x n).choose

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem Q_spec (x : WittVector p k₀) (n : ℕ) :
    x - (D.Q x n).eval₂ (Int.castRingHom _) D.u ∈ Ideal.span {(p : WittVector p k₀)} ^ n :=
  (D.density x n).choose_spec

attribute [irreducible] Q

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
include D in

theorem span_p_pow_le (n : ℕ) {x : 𝒪} (hx : x ∈ (Ideal.span {(p : 𝒪)} ^ n : Ideal 𝒪)) :
    x ∈ maximalIdeal 𝒪 ^ n :=
  Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).mpr D.p_mem) n hx

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem residue_eval₂_eq (P : ℤ[X]) :
    residue 𝒪 (P.eval₂ (Int.castRingHom 𝒪) D.v) =
      f (constantCoeff (P.eval₂ (Int.castRingHom (WittVector p k₀)) D.u)) := by
  rw [hom_eval₂, hom_eval₂, hom_eval₂, D.hvres,
    show (residue 𝒪).comp (Int.castRingHom 𝒪) = Int.castRingHom _ from RingHom.ext_int _ _,
    show (constantCoeff : WittVector p k₀ →+* k₀).comp (Int.castRingHom _) =
      Int.castRingHom k₀ from RingHom.ext_int _ _,
    show f.comp (Int.castRingHom k₀) = Int.castRingHom _ from RingHom.ext_int _ _]

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem sub_mem_of_smodEq {x y : 𝒪} {n : ℕ}
    (h : x ≡ y [SMOD ((maximalIdeal 𝒪) ^ n • (⊤ : Submodule 𝒪 𝒪))]) :
    x - y ∈ (maximalIdeal 𝒪) ^ n := by
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id] at h
  exact h

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem smodEq_of_sub_mem {x y : 𝒪} {n : ℕ} (h : x - y ∈ (maximalIdeal 𝒪) ^ n) :
    x ≡ y [SMOD ((maximalIdeal 𝒪) ^ n • (⊤ : Submodule 𝒪 𝒪))] := by
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id]
  exact h

omit [Finite k₀] [CharP k₀ p] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem cauchy (x : WittVector p k₀) {m n : ℕ} (hmn : m ≤ n) :
    (D.Q x m).eval₂ (Int.castRingHom _) D.v ≡ (D.Q x n).eval₂ (Int.castRingHom _) D.v
      [SMOD ((maximalIdeal 𝒪) ^ m • (⊤ : Submodule 𝒪 𝒪))] := by
  refine smodEq_of_sub_mem (D.span_p_pow_le m ?_)

  have h : (D.Q x m - D.Q x n).eval₂ (Int.castRingHom _) D.u ∈
      Ideal.span {(p : WittVector p k₀)} ^ m := by
    rw [eval₂_sub]
    have h1 := D.Q_spec x m
    have h2 := Ideal.pow_le_pow_right hmn (D.Q_spec x n)
    have := (Ideal.sub_mem _ h2 h1)
    rwa [sub_sub_sub_cancel_left] at this
  have := D.key _ m h
  rwa [eval₂_sub] at this

noncomputable def limVal (x : WittVector p k₀) : 𝒪 :=
  (IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := maximalIdeal 𝒪))
    (fun {_ _} => D.cauchy x)).choose

omit [Finite k₀] [CharP k₀ p] in
theorem limVal_spec (x : WittVector p k₀) (n : ℕ) :
    (D.Q x n).eval₂ (Int.castRingHom _) D.v ≡ D.limVal x
      [SMOD ((maximalIdeal 𝒪) ^ n • (⊤ : Submodule 𝒪 𝒪))] :=
  (IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := maximalIdeal 𝒪))
    (fun {_ _} => D.cauchy x)).choose_spec n

attribute [irreducible] limVal

omit [Finite k₀] [CharP k₀ p] in

theorem smodEq_limVal_of_approx (x : WittVector p k₀) (n : ℕ) (P : ℤ[X])
    (hP : x - P.eval₂ (Int.castRingHom _) D.u ∈ Ideal.span {(p : WittVector p k₀)} ^ n) :
    P.eval₂ (Int.castRingHom _) D.v ≡ D.limVal x
      [SMOD ((maximalIdeal 𝒪) ^ n • (⊤ : Submodule 𝒪 𝒪))] := by
  refine SModEq.trans ?_ (D.limVal_spec x n)
  refine smodEq_of_sub_mem (D.span_p_pow_le n ?_)
  have h : (P - D.Q x n).eval₂ (Int.castRingHom _) D.u ∈
      Ideal.span {(p : WittVector p k₀)} ^ n := by
    rw [eval₂_sub]
    have h1 := D.Q_spec x n
    have := (Ideal.sub_mem _ h1 hP)
    rwa [sub_sub_sub_cancel_left] at this
  have := D.key _ n h
  rwa [eval₂_sub] at this

omit [Finite k₀] [CharP k₀ p] in

theorem limVal_eval₂ (P : ℤ[X]) :
    D.limVal (P.eval₂ (Int.castRingHom _) D.u) = P.eval₂ (Int.castRingHom _) D.v := by
  symm
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal 𝒪)]
  exact fun n => D.smodEq_limVal_of_approx _ n P (by rw [sub_self]; exact Ideal.zero_mem _)

omit [Finite k₀] [CharP k₀ p] in

theorem limVal_add (x y : WittVector p k₀) : D.limVal (x + y) = D.limVal x + D.limVal y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal 𝒪)]
  intro n

  set P : ℤ[X] := D.Q x n + D.Q y n with hP
  have happ : (x + y) - P.eval₂ (Int.castRingHom (WittVector p k₀)) D.u ∈
      Ideal.span {(p : WittVector p k₀)} ^ n := by
    have h := Ideal.add_mem _ (D.Q_spec x n) (D.Q_spec y n)
    rwa [← add_sub_add_comm, ← eval₂_add, ← hP] at h
  refine smodEq_of_sub_mem ?_
  have h1 : D.limVal (x + y) - P.eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.smodEq_limVal_of_approx (x + y) n P happ).symm
  have h2 : D.limVal x - (D.Q x n).eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.limVal_spec x n).symm
  have h3 : D.limVal y - (D.Q y n).eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.limVal_spec y n).symm
  have heq : D.limVal (x + y) - (D.limVal x + D.limVal y) =
      (D.limVal (x + y) - P.eval₂ (Int.castRingHom 𝒪) D.v)
      - (D.limVal x - (D.Q x n).eval₂ (Int.castRingHom 𝒪) D.v)
      - (D.limVal y - (D.Q y n).eval₂ (Int.castRingHom 𝒪) D.v) := by
    rw [hP, eval₂_add]; ring
  rw [heq]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ h1 h2) h3

omit [Finite k₀] [CharP k₀ p] in
theorem limVal_mul (x y : WittVector p k₀) : D.limVal (x * y) = D.limVal x * D.limVal y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal 𝒪)]
  intro n
  set P : ℤ[X] := D.Q x n * D.Q y n with hP
  have happ : (x * y) - P.eval₂ (Int.castRingHom (WittVector p k₀)) D.u ∈
      Ideal.span {(p : WittVector p k₀)} ^ n := by
    have h := Ideal.add_mem _ (Ideal.mul_mem_right y _ (D.Q_spec x n))
      (Ideal.mul_mem_left _ ((D.Q x n).eval₂ (Int.castRingHom (WittVector p k₀)) D.u)
        (D.Q_spec y n))
    rwa [mul_sub, sub_mul, sub_add_sub_cancel, ← eval₂_mul, ← hP] at h
  refine smodEq_of_sub_mem ?_
  have h1 : D.limVal (x * y) - P.eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.smodEq_limVal_of_approx (x * y) n P happ).symm
  have h2 : D.limVal x - (D.Q x n).eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.limVal_spec x n).symm
  have h3 : D.limVal y - (D.Q y n).eval₂ (Int.castRingHom 𝒪) D.v ∈ maximalIdeal 𝒪 ^ n :=
    sub_mem_of_smodEq (D.limVal_spec y n).symm
  have heq : D.limVal (x * y) - D.limVal x * D.limVal y =
      (D.limVal (x * y) - P.eval₂ (Int.castRingHom 𝒪) D.v)
      - (D.limVal x - (D.Q x n).eval₂ (Int.castRingHom 𝒪) D.v) * D.limVal y
      - (D.Q x n).eval₂ (Int.castRingHom 𝒪) D.v *
          (D.limVal y - (D.Q y n).eval₂ (Int.castRingHom 𝒪) D.v) := by
    rw [hP, eval₂_mul]; ring
  rw [heq]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ h2))
    (Ideal.mul_mem_left _ _ h3)

omit [Finite k₀] [CharP k₀ p] in
theorem limVal_one : D.limVal 1 = 1 := by
  have h := D.limVal_eval₂ (1 : ℤ[X])
  rwa [eval₂_one, eval₂_one] at h

omit [Finite k₀] [CharP k₀ p] in
theorem limVal_zero : D.limVal 0 = 0 := by
  have h := D.limVal_eval₂ (0 : ℤ[X])
  rwa [eval₂_zero, eval₂_zero] at h

noncomputable def limHom : WittVector p k₀ →+* 𝒪 where
  toFun := D.limVal
  map_one' := D.limVal_one
  map_mul' := D.limVal_mul
  map_zero' := D.limVal_zero
  map_add' := D.limVal_add

theorem residue_limHom (x : WittVector p k₀) :
    residue 𝒪 (D.limHom x) = f (constantCoeff x) := by
  haveI : PerfectRing k₀ p := PerfectRing.ofFiniteOfIsReduced p k₀

  have hQu : x - (D.Q x 1).eval₂ (Int.castRingHom _) D.u ∈
      Ideal.span {(p : WittVector p k₀)} := by
    have := D.Q_spec x 1; rwa [pow_one] at this
  have hcc : constantCoeff ((D.Q x 1).eval₂ (Int.castRingHom _) D.u) = constantCoeff x := by
    have h : constantCoeff (x - (D.Q x 1).eval₂ (Int.castRingHom _) D.u) = 0 := by
      rw [← RingHom.mem_ker, ker_constantCoeff_eq_span]
      exact hQu
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  have hmod : D.limHom x - (D.Q x 1).eval₂ (Int.castRingHom _) D.v ∈ maximalIdeal 𝒪 := by
    have := sub_mem_of_smodEq (D.limVal_spec x 1).symm
    rwa [pow_one] at this
  have hres_eq : residue 𝒪 (D.limHom x) = residue 𝒪 ((D.Q x 1).eval₂ (Int.castRingHom _) D.v) := by
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmod
  rw [hres_eq, D.residue_eval₂_eq, hcc]

theorem isLocalHom_limHom : IsLocalHom D.limHom := by
  haveI : PerfectRing k₀ p := PerfectRing.ofFiniteOfIsReduced p k₀
  constructor
  intro x hx
  have hfcc : f (constantCoeff x) ≠ 0 := by
    rw [← D.residue_limHom x]
    intro h0
    exact (maximalIdeal.isMaximal 𝒪).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) hx)
  have hcc : x.coeff 0 ≠ 0 := fun h0 => hfcc (by
    rw [show constantCoeff x = x.coeff 0 from rfl, h0, map_zero])
  exact WittVector.isUnit_of_coeff_zero_ne_zero x hcc

end CohenData

theorem cohen_of_key_of_density (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (f : k₀ →+* ResidueField 𝒪)
    {u : WittVector p k₀} {v : 𝒪} (hvres : residue 𝒪 v = f (constantCoeff u))
    (key : ∀ (Q : ℤ[X]) (n : ℕ),
      Q.eval₂ (Int.castRingHom _) u ∈ Ideal.span {(p : WittVector p k₀)} ^ n →
      Q.eval₂ (Int.castRingHom _) v ∈ Ideal.span {(p : 𝒪)} ^ n)
    (density : ∀ (x : WittVector p k₀) (n : ℕ), ∃ Q : ℤ[X],
      x - Q.eval₂ (Int.castRingHom _) u ∈ Ideal.span {(p : WittVector p k₀)} ^ n) :
    ∃ g : WittVector p k₀ →+* 𝒪, IsLocalHom g ∧
      (residue 𝒪).comp g = f.comp (WittVector.constantCoeff : WittVector p k₀ →+* k₀) := by
  let D : CohenData (p := p) f := ⟨hp𝒪, u, v, hvres, key, density⟩
  exact ⟨D.limHom, D.isLocalHom_limHom, RingHom.ext D.residue_limHom⟩

end Limit

end W3Cohen

theorem solution (p : ℕ) [Fact p.Prime]
    (k₀ : Type) [Field k₀] [Finite k₀] [CharP k₀ p]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (f : k₀ →+* IsLocalRing.ResidueField 𝒪) :
    ∃ g : WittVector p k₀ →+* 𝒪, IsLocalHom g ∧
      (IsLocalRing.residue 𝒪).comp g =
        f.comp (WittVector.constantCoeff : WittVector p k₀ →+* k₀) := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := k₀ˣ)
  exact W3Cohen.cohen_of_key_of_density hp𝒪 f
    (u := WittVector.teichmuller p (c : k₀)) (v := W3Cohen.teich hp𝒪 f (c : k₀))
    (by rw [W3Cohen.residue_teich]; congr 1)
    (fun Q n h => by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h ⊢
      exact W3Cohen.pow_dvd_evalO_of_pow_dvd_evalW hp𝒪 f hc n Q h)
    (W3Cohen.density_teichmuller hc)

end S_WittVector_exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff
end P2MW
export P2MW.S_WittVector_exists_ringHom_isLocalHom_and_residue_comp_eq_comp_constantCoeff (solution)
