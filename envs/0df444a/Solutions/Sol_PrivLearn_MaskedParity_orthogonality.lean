-- Prove2me | solution 1 for PrivLearn.MaskedParity.orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:50:00.087374+00:00
-- url     : https://prove2.me/submissions/83119b38-44c1-4dbf-8a5b-da9146ee8c27

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle
set_option autoImplicit false
open PrivLearn.MaskedParity

noncomputable def epsZ (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

lemma z2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by revert u; decide

lemma z2_one_ne : (1 : ZMod 2) ≠ 0 := by decide
lemma z2_one_add : (1 : ZMod 2) + 1 = 0 := by decide

lemma epsZ_pow (z : ZMod 2) : (-1 : ℝ) ^ z.val = epsZ z := by
  rcases z2_cases z with rfl | rfl
  · simp [epsZ]
  · have : (1 : ZMod 2).val = 1 := rfl
    simp [epsZ, this, z2_one_ne]

lemma epsZ_add (u v : ZMod 2) : epsZ (u + v) = epsZ u * epsZ v := by
  rcases z2_cases u with rfl | rfl <;> rcases z2_cases v with rfl | rfl <;>
    simp [epsZ, z2_one_ne, z2_one_add]

lemma epsZ_sum {ι : Type*} (t : Finset ι) (z : ι → ZMod 2) :
    epsZ (∑ i ∈ t, z i) = ∏ i ∈ t, epsZ (z i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [epsZ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, epsZ_add, ih]

lemma epsZ_char_sum (d : ℕ) (s : Fin d → ZMod 2) :
    ∑ x : Fin d → ZMod 2, epsZ (s ⬝ᵥ x) = if s = 0 then (2 : ℝ) ^ d else 0 := by
  classical
  have h1 : ∀ x : Fin d → ZMod 2, epsZ (s ⬝ᵥ x) = ∏ i, epsZ (s i * x i) := by
    intro x; unfold dotProduct; exact epsZ_sum _ _
  simp_rw [h1]
  have h2 : ∑ x : Fin d → ZMod 2, ∏ i, epsZ (s i * x i) = ∏ i, ∑ z : ZMod 2, epsZ (s i * z) := by
    rw [Finset.prod_univ_sum]
    simp
  rw [h2]
  have h3 : ∀ c : ZMod 2, ∑ z : ZMod 2, epsZ (c * z) = if c = 0 then 2 else 0 := by
    intro c
    have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [hU, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    rcases z2_cases c with rfl | rfl
    · simp [epsZ]; norm_num
    · simp [epsZ]
  simp_rw [h3]
  by_cases hs : s = 0
  · subst hs; simp
  · have : ∃ i, s i ≠ 0 := by
      by_contra h; push_neg at h; exact hs (funext h)
    obtain ⟨i, hi⟩ := this
    rw [if_neg hs]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem solution {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (r r' : Fin d → ZMod 2) (a : ZMod 2) :
    ip (half 0 (cMP r a)) (half 0 (cMP r' a)) = if r = r' then 1 / 2 else 0 := by
  classical
  obtain ⟨m, hm⟩ := hd
  have hdpos : (0 : ℝ) < d := by rw [hm]; positivity
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := z2_cases
  -- the integrand
  have hF : ∀ u : Dom d, half 0 (cMP r a) u * half 0 (cMP r' a) u
      = if u.2.2 = 0 then epsZ ((r - r') ⬝ᵥ u.1) else 0 := by
    intro u
    obtain ⟨x, i, b⟩ := u
    rcases z2_cases b with rfl | rfl
    · simp only [half, cMP, if_true, epsZ_pow]
      rw [← epsZ_add]
      congr 1
      have key : ∀ p q a : ZMod 2, (p + a) + (q + a) = p - q := by decide
      rw [sub_dotProduct]
      exact key _ _ _
    · simp [half, z2_one_ne]
  have hcard : (Fintype.card (Dom d) : ℝ) = 2 ^ d * (d * 2) := by
    simp [Dom, Fintype.card_prod, Fintype.card_fun, ZMod.card]
  unfold ip
  simp_rw [hF]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hcard]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, epsZ_char_sum]
  have hsub : (r - r' = 0) ↔ r = r' := sub_eq_zero
  by_cases hrr : r = r'
  · rw [if_pos (hsub.mpr hrr), if_pos hrr]
    have h2 : (0 : ℝ) < 2 ^ d := by positivity
    field_simp
  · rw [if_neg (fun h => hrr (hsub.mp h)), if_neg hrr]
    simp
