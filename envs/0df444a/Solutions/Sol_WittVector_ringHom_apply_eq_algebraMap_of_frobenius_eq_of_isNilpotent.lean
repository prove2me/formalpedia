-- Prove2me | solution 1 for WittVector.ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a1d87532-a496-5bec-993a-d41acefb7f88

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent

set_option autoImplicit false

universe u v

open CerednikDrinfeld

namespace X2aSol

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_algebraMap_eq_of_pow_eq {L : Type} [Field L] [Algebra (ZMod p) L] (x : L) (hx : x ^ p = x) :
    ∃ c : ZMod p, algebraMap (ZMod p) L c = x := by
  classical
  by_contra hcon
  push Not at hcon
  have hp1 : 1 < p := hp.out.one_lt
  set f : Polynomial L := Polynomial.X ^ p - Polynomial.X with hf
  have hdeg : f.natDegree = p := by
    rw [hf, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp1]
  have hf0 : f ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; exact hp.out.ne_zero hdeg.symm
  have hinj : Function.Injective (algebraMap (ZMod p) L) := (algebraMap (ZMod p) L).injective
  let Z : Finset L := insert x ((Finset.univ : Finset (ZMod p)).image (algebraMap (ZMod p) L))
  have hZroots : Z.val ⊆ f.roots := by
    intro y hy
    rw [Finset.mem_val, Finset.mem_insert, Finset.mem_image] at hy
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot, hf, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rcases hy with rfl | ⟨c, -, rfl⟩
    · exact hx
    · rw [← map_pow, ZMod.pow_card c]
  have hcard : Z.card = p + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
    intro hxmem
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hxmem
    exact hcon c hc
  have := Polynomial.card_le_degree_of_subset_roots hZroots
  rw [hcard, hdeg] at this
  omega

theorem main {R : Type u} [CommRing R] (hpn : IsNilpotent (p : R)) {A : Type v} [Ring A] [Algebra R A]
    (ρ : Zp2 p →+* A) (j : Zp2 p →+* R) (a : Zp2 p) (ha : WittVector.frobenius a = a) :
    ρ a = algebraMap R A (j a) := by
  classical
  obtain ⟨N, hN⟩ := hpn

  have hc : ∀ n, ∃ c : ZMod p, algebraMap (ZMod p) (GaloisField p 2) c = a.coeff n := fun n =>
    exists_algebraMap_eq_of_pow_eq p (a.coeff n) (by rw [← WittVector.coeff_frobenius_charP, ha])
  choose c hcdef using hc
  have ha' : WittVector.map (algebraMap (ZMod p) (GaloisField p 2)) (WittVector.mk p c) = a := by
    ext n
    rw [WittVector.map_coeff, WittVector.coeff_mk]
    exact hcdef n

  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec N (WittVector.equiv p (WittVector.mk p c)))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, PadicInt.appr (WittVector.equiv p (WittVector.mk p c)) N = m := ⟨_, rfl⟩
  rw [hm] at hw
  have ha'eq : WittVector.mk p c = (m : WittVector p (ZMod p)) + (p : WittVector p (ZMod p)) ^ N * (WittVector.equiv p).symm w := by
    apply (WittVector.equiv p).injective
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, RingEquiv.apply_symm_apply]
    linear_combination (-1 : ℤ_[p]) * hw
  have haeq : a = (m : Zp2 p) +
      (p : Zp2 p) ^ N * WittVector.map (algebraMap (ZMod p) (GaloisField p 2)) ((WittVector.equiv p).symm w) := by
    rw [← ha', ha'eq, map_add, map_mul, map_pow, map_natCast, map_natCast]

  have hpA : (p : A) ^ N = 0 := by
    rw [← map_natCast (algebraMap R A), ← map_pow, hN, map_zero]
  rw [haeq]
  simp only [map_add, map_mul, map_pow, map_natCast, hpA, zero_mul, add_zero]

end X2aSol

open CerednikDrinfeld in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (hp : IsNilpotent (p : R))
    {A : Type v} [Ring A] [Algebra R A]
    (ρ : Zp2 p →+* A) (j : Zp2 p →+* R) (a : Zp2 p) (ha : WittVector.frobenius a = a) :
    ρ a = algebraMap R A (j a) :=
  X2aSol.main p hp ρ j a ha

end S_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent
end P2MW
export P2MW.S_WittVector_ringHom_apply_eq_algebraMap_of_frobenius_eq_of_isNilpotent (solution)
