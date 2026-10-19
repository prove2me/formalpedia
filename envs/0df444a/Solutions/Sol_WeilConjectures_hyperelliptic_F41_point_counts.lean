-- Prove2me | solution 1 for WeilConjectures.hyperelliptic_F41_point_counts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:07:46.569099+00:00
-- url     : https://prove2.me/submissions/50a9b49f-a44b-4d09-96bc-ed16713a53b1

import Mathlib

namespace WEPC

abbrev P := ZMod 41 × ZMod 41
def pmul (u v : P) : P := (u.1 * v.1 + 3 * u.2 * v.2, u.1 * v.2 + u.2 * v.1)
def psq (u : P) : P := pmul u u
def pow105 (u : P) : P :=
  let u2 := psq u; let u4 := psq u2; let u8 := psq u4; let u16 := psq u8
  let u32 := psq u16; let u64 := psq u32
  pmul (pmul (pmul u64 u32) u8) u
def pow840 (u : P) : P := psq (psq (psq (pow105 u)))
def pow5 (u : P) : P := pmul (psq (psq u)) u
def chiP (d : P) : ℤ := if d = (0, 0) then 0 else if pow840 d = (1, 0) then 1 else -1
def E (u : P) : P := (1 + 4 * (pow5 u).1, 4 * (pow5 u).2)

set_option maxRecDepth 100000 in
lemma sum_val : ∑ u : P, chiP (E u) = 61 := by decide

end WEPC

namespace WEPC

set_option maxRecDepth 100000 in
lemma part1 : Fintype.card {xy : ZMod 41 × ZMod 41 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} = 32 := by decide

lemma no_sqrt3 : ∀ u : ZMod 41, u ^ 2 ≠ 3 := by decide

end WEPC

namespace WEPC
set_option maxRecDepth 100000 in
lemma three_pow : (3 : ZMod 41) ^ (1681 / 2) = 1 := by decide
end WEPC


namespace WEPC
open Finset

variable [Fact (Nat.Prime 41)]

noncomputable instance instFTG : Fintype (GaloisField 41 2) := Fintype.ofFinite _

open Classical in
lemma cardG : Fintype.card (GaloisField 41 2) = 1681 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 41 2 (by norm_num)]; norm_num

lemma charG : ringChar (GaloisField 41 2) = 41 := ringChar.eq (GaloisField 41 2) 41

lemma hF : ringChar (GaloisField 41 2) ≠ 2 := by rw [charG]; norm_num

lemma two_ne : (2 : GaloisField 41 2) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField 41 2) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField 41 2) 41] at h'
  norm_num at h'

lemma alg3 : algebraMap (ZMod 41) (GaloisField 41 2) 3 = 3 := map_ofNat _ 3
lemma alg4 : algebraMap (ZMod 41) (GaloisField 41 2) 4 = 4 := map_ofNat _ 4

open Classical in
lemma exists_alpha : ∃ α : GaloisField 41 2, α ^ 2 = 3 := by
  have h3 : (3 : GaloisField 41 2) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : GaloisField 41 2) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 41 2) 41] at h'
    norm_num at h'
  have hχ : ((quadraticChar (GaloisField 41 2) 3 : ℤ) : GaloisField 41 2) = 1 := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hF, cardG]
    have := congrArg (algebraMap (ZMod 41) (GaloisField 41 2)) three_pow
    rw [map_pow, map_one, alg3] at this
    exact this
  have : quadraticChar (GaloisField 41 2) 3 = 1 := by
    rcases quadraticChar_dichotomy h3 with h | h
    · exact h
    · rw [h] at hχ; push_cast at hχ
      exfalso; apply two_ne; linear_combination -hχ
  obtain ⟨b, hb⟩ := (quadraticChar_one_iff_isSquare h3).1 this
  exact ⟨b, by rw [sq]; exact hb.symm⟩

noncomputable def phi (α : GaloisField 41 2) (u : P) : GaloisField 41 2 :=
  algebraMap (ZMod 41) (GaloisField 41 2) u.1 + algebraMap (ZMod 41) (GaloisField 41 2) u.2 * α

section
variable (α : GaloisField 41 2) (hα : α ^ 2 = 3)
include hα

lemma phi_mul (u v : P) : phi α (pmul u v) = phi α u * phi α v := by
  simp only [phi, pmul, map_add, map_mul, alg3]
  linear_combination (-(algebraMap (ZMod 41) (GaloisField 41 2) u.2 *
    algebraMap (ZMod 41) (GaloisField 41 2) v.2)) * hα

lemma phi_inj : Function.Injective (phi α) := by
  intro u v h
  simp only [phi] at h
  have h2 : algebraMap (ZMod 41) (GaloisField 41 2) (u.1 - v.1) +
      algebraMap (ZMod 41) (GaloisField 41 2) (u.2 - v.2) * α = 0 := by
    rw [map_sub, map_sub]; linear_combination h
  by_cases hb : u.2 = v.2
  · rw [hb, sub_self, map_zero, zero_mul, add_zero] at h2
    have : u.1 - v.1 = 0 := (algebraMap (ZMod 41) (GaloisField 41 2)).injective (by rw [h2, map_zero])
    exact Prod.ext (sub_eq_zero.1 this) hb
  · exfalso
    have hb' : u.2 - v.2 ≠ 0 := sub_ne_zero.2 hb
    have hbG : algebraMap (ZMod 41) (GaloisField 41 2) (u.2 - v.2) ≠ 0 := by
      rw [map_ne_zero]; exact hb'
    have hα' : α = algebraMap (ZMod 41) (GaloisField 41 2) (-(u.1 - v.1) / (u.2 - v.2)) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h2
    apply no_sqrt3 (-(u.1 - v.1) / (u.2 - v.2))
    apply (algebraMap (ZMod 41) (GaloisField 41 2)).injective
    rw [map_pow, ← hα', hα, alg3]

lemma phi_bij : Function.Bijective (phi α) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨phi_inj α hα, ?_⟩
  rw [cardG]; simp [Fintype.card_prod, ZMod.card]

lemma phi_pow840 (u : P) : phi α (pow840 u) = phi α u ^ 840 := by
  simp only [pow840, pow105, psq, phi_mul α hα]
  ring

lemma phi_E (u : P) : phi α (E u) = 1 + 4 * phi α u ^ 5 := by
  have h1 : phi α (E u) = 1 + 4 * phi α (pow5 u) := by
    simp only [phi, E, map_add, map_mul, map_one, alg4]; ring
  rw [h1]
  simp only [pow5, psq, phi_mul α hα]
  ring

lemma phi_zero : phi α (0, 0) = 0 := by simp [phi]
lemma phi_one : phi α (1, 0) = 1 := by simp [phi]

open Classical in
lemma chi_link (d : P) : quadraticChar (GaloisField 41 2) (phi α d) = chiP d := by
  unfold chiP
  have hc := quadraticChar_eq_pow_of_char_ne_two' hF (phi α d)
  rw [cardG, show 1681 / 2 = 840 from rfl, ← phi_pow840 α hα] at hc
  split_ifs with h0 h1
  · rw [h0, phi_zero α hα, quadraticChar_zero]
  · have hne : phi α d ≠ 0 := fun h => h0 (phi_inj α hα (h.trans (phi_zero α hα).symm))
    rw [h1, phi_one α hα] at hc
    rcases quadraticChar_dichotomy hne with h | h
    · exact h
    · rw [h] at hc; push_cast at hc
      exfalso; apply two_ne; linear_combination -hc
  · have hne : phi α d ≠ 0 := fun h => h0 (phi_inj α hα (h.trans (phi_zero α hα).symm))
    rcases quadraticChar_dichotomy hne with h | h
    · exfalso
      rw [h] at hc; push_cast at hc
      exact h1 (phi_inj α hα (hc.symm.trans (phi_one α hα).symm))
    · exact h
end

open Classical in
lemma count_fiber (c : GaloisField 41 2) :
    ((#{y : GaloisField 41 2 | y ^ 2 + y = c} : ℕ) : ℤ) = quadraticChar (GaloisField 41 2) (1 + 4 * c) + 1 := by
  rw [← quadraticChar_card_sqrts hF]
  congr 1
  have h2 := two_ne
  refine Finset.card_bij' (fun y _ => 2 * y + 1) (fun s _ => (s - 1) / 2) ?_ ?_ ?_ ?_
  · intro y hy
    have hy' : y ^ 2 + y = c := (Finset.mem_filter.1 hy).2
    have : (2 * y + 1) ^ 2 = 1 + 4 * c := by linear_combination 4 * hy'
    simpa using this
  · intro s hs
    have hs' : s ^ 2 = 1 + 4 * c := by simpa using hs
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    field_simp
    linear_combination hs'
  · intro y _; field_simp; ring
  · intro s _; field_simp; ring

open Classical in
lemma partG : Nat.card {xy : GaloisField 41 2 × GaloisField 41 2 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} = 1742 := by
  obtain ⟨α, hα⟩ := exists_alpha
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have hin : ∀ x : GaloisField 41 2, (∑ y : GaloisField 41 2, if y ^ 2 + y = x ^ 5 then 1 else 0) =
      #{y : GaloisField 41 2 | y ^ 2 + y = x ^ 5} := by
    intro x; rw [Finset.card_filter]
  simp only [hin]
  have hz : ((∑ x : GaloisField 41 2, #{y : GaloisField 41 2 | y ^ 2 + y = x ^ 5} : ℕ) : ℤ) = 1742 := by
    push_cast
    simp only [count_fiber]
    rw [Finset.sum_add_distrib]
    rw [← (phi_bij α hα).sum_comp (fun x => quadraticChar (GaloisField 41 2) (1 + 4 * x ^ 5))]
    simp only [← phi_E α hα, chi_link α hα, sum_val]
    simp [cardG]
  exact_mod_cast hz

end WEPC

theorem solution [Fact (Nat.Prime 41)] :
    Nat.card {xy : ZMod 41 × ZMod 41 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1 = 33 ∧
    Nat.card {xy : GaloisField 41 2 × GaloisField 41 2 // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1 = 1743 := by
  constructor
  · rw [Nat.card_eq_fintype_card, WEPC.part1]
  · rw [WEPC.partG]
