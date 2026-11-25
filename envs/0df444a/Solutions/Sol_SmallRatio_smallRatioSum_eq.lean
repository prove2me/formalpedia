-- Prove2me | solution 1 for SmallRatio.smallRatioSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:11.673815+00:00
-- url     : https://prove2.me/submissions/4d6f1dd6-5fef-4ae6-9cd6-f8513ebc753a

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
public import Theorems.Thm_SmallRatio_coprime_p_h
public import Theorems.Thm_SmallRatio_coprime_rem_den
public import Theorems.Thm_SmallRatio_den_congr
public import Theorems.Thm_SmallRatio_den_le
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_pos
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_legendre_pairing
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_le_h
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_strictAnti
public import Theorems.Thm_SmallRatio_rem_zero
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
namespace SmallRatio
theorem _root_.solution :
    smallRatioSum p h = ∑ i ∈ Icc 1 (steps p h),
      if 2 * rem p h i * den p h i < p then
        (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0 := by
  have hc := coprime_p_h hp hh hhp
  have : Fact p.Prime := ⟨hp⟩
  unfold smallRatioSum
  rw [← sum_product']
  symm
  apply sum_bij_ne_zero (fun i _ _ => (rem p h i, den p h i))
  · intro i hi hne
    rw [mem_Icc] at hi
    simp only [mem_product, mem_Icc]
    have hr := pos_rem_of_le_steps hh hhp hc hi.2
    have hrh := rem_le_h hh hhp hc hi.1 hi.2
    have hd := den_pos hh hhp hc hi.1 (by omega)
    have hdl := den_le hh hhp hc hi.1 hi.2
    omega
  · intro i hi _ j hj _ hij
    simp only [Prod.mk.injEq] at hij
    rw [mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := rem_strictAnti hh hhp hc hlt hj.2; omega
    · have := rem_strictAnti hh hhp hc hlt hi.2; omega
  · rintro ⟨u, v⟩ huv hne
    simp only [mem_product, mem_Icc] at huv
    by_cases hcond : Nat.Coprime u v ∧ 2 * u * v < p
    · rw [if_pos hcond] at hne
      -- one of the two congruences holds
      have hcong : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((h * v : ℕ) : ZMod p) = (ε : ZMod p) * u := by
        by_cases h1 : ((h * v : ℕ) : ZMod p) = (u : ZMod p)
        · exact ⟨1, Or.inl rfl, by simp [h1]⟩
        · by_cases h2 : ((h * v : ℕ) : ZMod p) = -(u : ZMod p)
          · exact ⟨-1, Or.inr rfl, by simp [h2]⟩
          · rw [if_neg h1, if_neg h2] at hne; simp at hne
      obtain ⟨ε, hε, hcg⟩ := hcong
      have hdvd : (p : ℤ) ∣ (h : ℤ) * v - ε * u := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hcg ⊢
        rw [hcg]; ring
      obtain ⟨j, hj, hju, hjv, hjε⟩ := legendre_pairing hh hhp hc u v huv.1.1 huv.2.1 hcond.1
        hcond.2 ε hε hdvd
      refine ⟨j, hj, ?_, by simp [hju, hjv]⟩
      rw [hju, hjv, if_pos hcond.2]
      have : (u : ℚ) * v ≠ 0 := by
        have : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
        have : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
        positivity
      rw [div_ne_zero_iff]
      exact ⟨by simp, this⟩
    · rw [if_neg hcond] at hne; exact absurd rfl hne
  · intro i hi hne
    rw [mem_Icc] at hi
    have hsmall : 2 * rem p h i * den p h i < p := by
      by_contra hs; rw [if_neg hs] at hne; exact hne rfl
    rw [if_pos hsmall]
    have hcop := coprime_rem_den hp hh hhp hi.1 hi.2
    simp only
    rw [if_pos ⟨hcop, hsmall⟩]
    -- the congruence `h Q_i ≡ (-1)^{i+1} r_i`
    have hcg := den_congr (k := p) (h := h) i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hcg
    push_cast at hcg
    have hcg' : ((h * den p h i : ℕ) : ZMod p) = (-1) ^ (i + 1) * (rem p h i : ZMod p) := by
      push_cast; linear_combination hcg
    have hr := pos_rem_of_le_steps hh hhp hc hi.2
    -- `r ≢ -r`
    have hne2 : (rem p h i : ZMod p) ≠ -(rem p h i : ZMod p) := by
      intro heq
      have h2 : ((2 * rem p h i : ℕ) : ZMod p) = 0 := by push_cast; linear_combination heq
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by omega) h2
      have hd := den_pos hh hhp hc hi.1 (by omega)
      have : 2 * rem p h i ≤ 2 * rem p h i * den p h i := Nat.le_mul_of_pos_right _ hd
      omega
    rcases Nat.even_or_odd i with he | ho
    · have hs : (-1 : ZMod p) ^ (i + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      have hs' : (-1 : ℚ) ^ (i + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      rw [hs, neg_one_mul] at hcg'
      rw [if_neg (by rw [hcg']; exact fun h => hne2 h.symm), if_pos hcg', hs']
      ring
    · have hs : (-1 : ZMod p) ^ (i + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
      have hs' : (-1 : ℚ) ^ (i + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
      rw [hs, one_mul] at hcg'
      rw [if_pos hcg', if_neg (by rw [hcg']; exact hne2), hs']
      ring
end SmallRatio
