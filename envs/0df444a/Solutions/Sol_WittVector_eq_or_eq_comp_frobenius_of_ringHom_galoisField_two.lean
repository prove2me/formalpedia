-- Prove2me | solution 1 for WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/56af182d-ccb4-5090-9ae5-64b5baaeef29

import Mathlib
import Theorems.Thm_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace R4Iota

open WittVector

variable {p : ℕ} [hp : Fact p.Prime]

section perfect

variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p]

theorem coeff_zero_p_mul (y : WittVector p k) : ((p : WittVector p k) * y).coeff 0 = 0 := by
  rw [mul_comm]; exact WittVector.mul_charP_coeff_zero y

theorem p_dvd_of_coeff_zero (x : WittVector p k) (hx : x.coeff 0 = 0) : (p : WittVector p k) ∣ x := by
  by_cases h0 : x = 0
  · rw [h0]; exact dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => rw [pow_zero, one_mul] at hx; exact absurd hx hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ]; ring⟩

theorem eq_zero_of_forall_pow_dvd (d : WittVector p k) (h : ∀ n : ℕ, (p : WittVector p k) ^ n ∣ d) : d = 0 := by
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul d h0
  obtain ⟨c, hc⟩ := h (m + 1)
  have hpm : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero _ (by
    intro h
    have := congrArg (fun x : WittVector p k => x.coeff 1) h
    simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
    exact one_ne_zero this)
  have : b = (p : WittVector p k) * c := by
    apply mul_left_cancel₀ hpm
    rw [hc, pow_succ, mul_assoc]
  rw [this, coeff_zero_p_mul] at hb
  exact hb rfl

theorem pow_dvd_pow_sub_pow {R : Type*} [CommRing R] {a b : R} (hab : (p : R) ∣ a - b) (n : ℕ)
    (h : (p : R) ^ (n + 1) ∣ a - b) : (p : R) ^ (n + 2) ∣ a ^ p - b ^ p := by
  rw [← geom_sum₂_mul, show n + 2 = 1 + (n + 1) by ring, pow_add, pow_one]
  refine mul_dvd_mul ?_ h
  let f : R →+* R ⧸ Ideal.span {(p : R)} := Ideal.Quotient.mk (Ideal.span {(p : R)})
  have hf : ∀ r : R, (p : R) ∣ r ↔ f r = 0 := fun r ↦ by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hf, map_sub, sub_eq_zero] at hab
  rw [hf, RingHom.map_geom_sum₂, hab, geom_sum₂_self, mul_eq_zero_of_left]
  rw [← map_natCast f, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem eq_of_pow_eq_of_p_dvd (y t : WittVector p k) (hy : y ^ (p ^ 2) = y) (ht : t ^ (p ^ 2) = t)
    (h : (p : WittVector p k) ∣ y - t) : y = t := by
  have key : ∀ n : ℕ, (p : WittVector p k) ^ (n + 1) ∣ y - t := by
    intro n
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      have h1 : (p : WittVector p k) ^ (n + 2) ∣ y ^ p - t ^ p := pow_dvd_pow_sub_pow h n ih
      have hab' : (p : WittVector p k) ∣ y ^ p - t ^ p :=
        (dvd_pow_self _ (by omega : n + 2 ≠ 0)).trans h1
      have h2 : (p : WittVector p k) ^ (n + 3) ∣ (y ^ p) ^ p - (t ^ p) ^ p := pow_dvd_pow_sub_pow hab' (n + 1) h1
      rw [← pow_mul, ← pow_mul, ← pow_two, hy, ht] at h2
      exact (pow_dvd_pow _ (by omega : n + 1 + 1 ≤ n + 3)).trans h2
  have : y - t = 0 := eq_zero_of_forall_pow_dvd _ fun n =>
    (pow_dvd_pow _ (Nat.le_succ n)).trans (key n)
  exact sub_eq_zero.mp this

theorem eq_teichmuller_of_pow_eq (y : WittVector p k) (hy : y ^ (p ^ 2) = y) :
    y = WittVector.teichmuller p (y.coeff 0) := by
  have h0 : (y.coeff 0) ^ (p ^ 2) = y.coeff 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) hy
    rwa [map_pow] at this
  refine eq_of_pow_eq_of_p_dvd y _ hy ?_ ?_
  · rw [← map_pow, h0]
  · apply p_dvd_of_coeff_zero
    have := (WittVector.constantCoeff : WittVector p k →+* k).map_sub y (WittVector.teichmuller p (y.coeff 0))
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at this
    exact this

end perfect

section source

variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p]

local notation "F" => GaloisField p 2

scoped instance : Fintype (GaloisField p 2) := Fintype.ofFinite _
scoped instance : PerfectRing (GaloisField p 2) p := PerfectField.toPerfectRing p

theorem card_F : Fintype.card (GaloisField p 2) = p ^ 2 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]

theorem pow_card_F (f : GaloisField p 2) : f ^ (p ^ 2) = f := by
  have := FiniteField.pow_card f; rwa [card_F] at this

theorem teichmuller_pow_card (f : GaloisField p 2) :
    (WittVector.teichmuller p f) ^ (p ^ 2) = WittVector.teichmuller p f := by
  rw [← map_pow, pow_card_F]

theorem frobenius_teichmuller (f : GaloisField p 2) :
    WittVector.frobenius (WittVector.teichmuller p f) = WittVector.teichmuller p (f ^ p) := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  cases n with
  | zero =>
    show ((WittVector.teichmuller p f).coeff 0) ^ p = (WittVector.teichmuller p (f ^ p)).coeff 0
    rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  | succ n =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n), WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n),
      zero_pow hp.out.ne_zero]

variable (a : WittVector p (GaloisField p 2) →+* WittVector p k)

theorem constantCoeff_surjective : Function.Surjective (WittVector.constantCoeff : WittVector p (GaloisField p 2) →+* GaloisField p 2) :=
  fun f => ⟨WittVector.teichmuller p f, WittVector.teichmuller_coeff_zero p f⟩

theorem ker_le : RingHom.ker (WittVector.constantCoeff : WittVector p (GaloisField p 2) →+* GaloisField p 2) ≤
    RingHom.ker ((WittVector.constantCoeff : WittVector p k →+* k).comp a) := by
  intro x hx
  rw [RingHom.mem_ker, WittVector.constantCoeff_apply] at hx
  obtain ⟨z, rfl⟩ := p_dvd_of_coeff_zero x hx
  rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, WittVector.constantCoeff_apply, coeff_zero_p_mul]

def red : GaloisField p 2 →+* k :=
  (WittVector.constantCoeff : WittVector p (GaloisField p 2) →+* GaloisField p 2).liftOfSurjective
    constantCoeff_surjective ⟨(WittVector.constantCoeff : WittVector p k →+* k).comp a, ker_le a⟩

theorem red_coeff_zero (x : WittVector p (GaloisField p 2)) : red a (x.coeff 0) = (a x).coeff 0 := by
  have := (WittVector.constantCoeff : WittVector p (GaloisField p 2) →+* GaloisField p 2).liftOfRightInverse_comp_apply
    _ (Function.rightInverse_surjInv constantCoeff_surjective) ⟨(WittVector.constantCoeff : WittVector p k →+* k).comp a, ker_le a⟩ x
  exact this

theorem red_apply (f : GaloisField p 2) : red a f = (a (WittVector.teichmuller p f)).coeff 0 := by
  rw [← red_coeff_zero a, WittVector.teichmuller_coeff_zero]

theorem map_teichmuller (f : GaloisField p 2) :
    a (WittVector.teichmuller p f) = WittVector.teichmuller p (red a f) := by
  rw [red_apply]
  apply eq_teichmuller_of_pow_eq
  rw [← map_pow, teichmuller_pow_card]

theorem ringHom_padicInt_eq (g h : ℤ_[p] →+* WittVector p k) : g = h := by
  refine RingHom.ext fun z => ?_
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_pow_dvd
  intro n
  have hz := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨c, hc⟩ := hz
  have : z = (PadicInt.appr z n : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by rw [← hc]; ring
  refine ⟨g c - h c, ?_⟩
  conv_lhs => rw [this]
  rw [map_add, map_add, map_natCast, map_natCast, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  ring

theorem ringHom_witt_zmod_eq (g h : WittVector p (ZMod p) →+* WittVector p k) : g = h := by
  have := ringHom_padicInt_eq (g.comp (WittVector.equiv p).symm.toRingHom) (h.comp (WittVector.equiv p).symm.toRingHom)
  have h2 := congrArg (fun φ : ℤ_[p] →+* WittVector p k => φ.comp (WittVector.equiv p).toRingHom) this
  simpa [RingHom.comp_assoc] using h2

theorem embeddings (g h : GaloisField p 2 →+* k) :
    g = h ∨ g = h.comp (frobenius (GaloisField p 2) p) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI hAlg : Algebra (GaloisField p 2) k := h.toAlgebra
  have hcomm : ∀ (φ : GaloisField p 2 →+* k), (φ.comp (algebraMap (ZMod p) (GaloisField p 2))) = algebraMap (ZMod p) k :=
    fun φ => RingHom.ext_zmod _ _
  haveI : IsScalarTower (ZMod p) (GaloisField p 2) k :=
    IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun (hcomm h) x).symm
  let gA : GaloisField p 2 →ₐ[ZMod p] k :=
    { g with commutes' := fun x => DFunLike.congr_fun (hcomm g) x }
  let τ : GaloisField p 2 →ₐ[ZMod p] GaloisField p 2 := gA.restrictNormal (GaloisField p 2)
  have hτ : ∀ x, h (τ x) = g x := fun x => by
    have := gA.restrictNormal_commutes (GaloisField p 2) x
    exact this

  obtain ⟨⟨n, hn⟩, hτn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p 2)).2 τ
  rw [GaloisField.finrank p (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have hfrob : ∀ x : GaloisField p 2, FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p 2) x = x ^ p := fun x => by
    rw [FiniteField.coe_frobeniusAlgHom, ZMod.card]
  interval_cases n
  · left
    ext x
    rw [← hτ x, ← hτn]
    simp
  · right
    ext x
    rw [← hτ x, ← hτn]
    simp only [pow_one, RingHom.comp_apply]
    rw [hfrob]
    rfl

theorem map_frobenius_wittMap (z : WittVector p (ZMod p)) :
    WittVector.frobenius (WittVector.map (algebraMap (ZMod p) (GaloisField p 2)) z) =
      WittVector.map (algebraMap (ZMod p) (GaloisField p 2)) z := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow, ← WittVector.coeff_frobenius_charP,
    WittVector.frobenius_zmodp]

theorem main (b : WittVector p (GaloisField p 2) →+* WittVector p k) :
    a = b ∨ a = b.comp (WittVector.frobenius : WittVector p (GaloisField p 2) →+* WittVector p (GaloisField p 2)) := by

  let bF := Module.finBasis (ZMod p) (GaloisField p 2)
  have hbij := WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing p bF
  set m : WittVector p (ZMod p) →+* WittVector p (GaloisField p 2) := WittVector.map (algebraMap (ZMod p) (GaloisField p 2))
    with hm

  have hm_eq : ∀ (c : WittVector p (GaloisField p 2) →+* WittVector p k) (z : WittVector p (ZMod p)), a (m z) = c (m z) :=
    fun c z => DFunLike.congr_fun (ringHom_witt_zmod_eq (a.comp m) (c.comp m)) z

  rcases embeddings (red a) (red b) with hred | hred
  · left
    apply RingHom.ext
    intro x
    obtain ⟨c, rfl⟩ := hbij.2 x
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hm_eq b, map_teichmuller a, map_teichmuller b, hred]
  · right
    apply RingHom.ext
    intro x
    obtain ⟨c, rfl⟩ := hbij.2 x
    simp only [map_sum, map_mul, RingHom.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hm_eq (b.comp WittVector.frobenius), RingHom.comp_apply, map_frobenius_wittMap, map_teichmuller a, hred,
      RingHom.comp_apply, frobenius_teichmuller, map_teichmuller b]
    rfl

end source

end R4Iota
p2m_reactivate "P2MW.S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two.R4Iota"

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (a b : WittVector p (GaloisField p 2) →+* WittVector p k) :
    a = b ∨
      a = b.comp (WittVector.frobenius : WittVector p (GaloisField p 2) →+* WittVector p (GaloisField p 2)) :=
  R4Iota.main a b

end
end S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
end P2MW
export P2MW.S_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two (solution)
