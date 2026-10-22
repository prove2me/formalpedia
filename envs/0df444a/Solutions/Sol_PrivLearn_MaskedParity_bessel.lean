-- Prove2me | solution 1 for PrivLearn.MaskedParity.bessel
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:06:47.940822+00:00
-- url     : https://prove2.me/submissions/99008db0-96eb-4687-8506-59834738ed00

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


lemma add_eq_zero_iff_eq' {d : ℕ} (x y : Fin d → ZMod 2) : x + y = 0 ↔ y = x := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    revert this; generalize x i = a; generalize y i = b; revert a b; decide
  · intro h; subst h; funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize y i = a; revert a; decide

lemma parseval {d : ℕ} (G : (Fin d → ZMod 2) → ℝ) :
    ∑ r : Fin d → ZMod 2, (∑ x, G x * epsZ (r ⬝ᵥ x)) ^ 2 = 2 ^ d * ∑ x, G x ^ 2 := by
  classical
  have h1 : ∀ r : Fin d → ZMod 2, (∑ x, G x * epsZ (r ⬝ᵥ x)) ^ 2
      = ∑ x, ∑ y, G x * G y * (epsZ (r ⬝ᵥ x) * epsZ (r ⬝ᵥ y)) := by
    intro r
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : Fin d → ZMod 2, ∑ r : Fin d → ZMod 2, ∑ y, G x * G y * (epsZ (r ⬝ᵥ x) * epsZ (r ⬝ᵥ y))
      = G x ^ 2 * 2 ^ d := by
    intro x
    rw [Finset.sum_comm]
    have h3 : ∀ y : Fin d → ZMod 2, ∑ r : Fin d → ZMod 2, G x * G y * (epsZ (r ⬝ᵥ x) * epsZ (r ⬝ᵥ y))
        = G x * G y * (if y = x then (2 : ℝ) ^ d else 0) := by
      intro y
      rw [← Finset.mul_sum]
      congr 1
      have h4 : ∀ r : Fin d → ZMod 2, epsZ (r ⬝ᵥ x) * epsZ (r ⬝ᵥ y) = epsZ ((x + y) ⬝ᵥ r) := by
        intro r
        rw [← epsZ_add, add_dotProduct, dotProduct_comm x r, dotProduct_comm y r]
      simp_rw [h4]
      rw [epsZ_char_sum]
      simp only [add_eq_zero_iff_eq']
    simp_rw [h3]
    simp [mul_ite, mul_zero]
    ring
  simp_rw [h2]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem solution {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) (g : Dom d → ℝ → ℝ)
    (hg : ∀ u y, (y = 1 ∨ y = -1) → (g u y = 1 ∨ g u y = -1)) :
    ∑ ra : (Fin d → ZMod 2) × ZMod 2, 2 * ip (half 0 (fg g)) (half 0 (cMP ra.1 ra.2)) ^ 2 ≤ 1 := by
  classical
  obtain ⟨m, hm⟩ := hd
  have hdpos : (0 : ℝ) < d := by rw [hm]; push_cast; positivity
  have hf : ∀ u, |fg g u| ≤ 1 := by
    intro u
    rcases hg u 1 (Or.inl rfl) with h1 | h1 <;> rcases hg u (-1) (Or.inr rfl) with h2 | h2 <;>
      simp [fg, h1, h2] <;> norm_num
  set G : (Fin d → ZMod 2) → ℝ := fun x => ∑ i, fg g (x, i, 0) with hGdef
  have hG : ∀ x, G x ^ 2 ≤ (d : ℝ) ^ 2 := by
    intro x
    have : |G x| ≤ d := by
      calc |G x| ≤ ∑ i, |fg g (x, i, 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => hf _
        _ = d := by simp
    exact (sq_le_sq' (by linarith [abs_nonneg (G x), neg_abs_le (G x)]) (le_trans (le_abs_self _) this))
  have hcard : (Fintype.card (Dom d) : ℝ) = 2 ^ d * (d * 2) := by
    simp [Dom, Fintype.card_prod, Fintype.card_fun, ZMod.card]
  have hip : ∀ (r : Fin d → ZMod 2) (a : ZMod 2),
      ip (half 0 (fg g)) (half 0 (cMP r a))
        = (2 ^ d * (d * 2 : ℝ))⁻¹ * (epsZ a * ∑ x, G x * epsZ (r ⬝ᵥ x)) := by
    intro r a
    unfold ip
    rw [hcard]
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp_rw [hU, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    simp only [half, cMP, if_true, epsZ_pow, z2_one_ne, if_false, mul_zero, add_zero]
    simp only [hGdef, Finset.sum_mul, Finset.mul_sum, ← epsZ_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm (r ⬝ᵥ x) a, epsZ_add]
    ring
  have hsum : ∀ r : Fin d → ZMod 2, ∑ a : ZMod 2, 2 * ip (half 0 (fg g)) (half 0 (cMP r a)) ^ 2
      = 4 * ((2 ^ d * (d * 2 : ℝ))⁻¹) ^ 2 * (∑ x, G x * epsZ (r ⬝ᵥ x)) ^ 2 := by
    intro r
    have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    simp_rw [hip, hU, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    simp [epsZ, z2_one_ne]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [hsum]
  rw [← Finset.mul_sum, parseval]
  have hP : (0 : ℝ) < 2 ^ d := by positivity
  have hS : ∑ x, G x ^ 2 ≤ 2 ^ d * (d : ℝ) ^ 2 := by
    calc ∑ x, G x ^ 2 ≤ ∑ _x : Fin d → ZMod 2, (d : ℝ) ^ 2 := Finset.sum_le_sum fun x _ => hG x
      _ = 2 ^ d * (d : ℝ) ^ 2 := by simp [Finset.sum_const, Fintype.card_fun, ZMod.card]
  calc 4 * ((2 ^ d * (d * 2 : ℝ))⁻¹) ^ 2 * (2 ^ d * ∑ x, G x ^ 2)
      ≤ 4 * ((2 ^ d * (d * 2 : ℝ))⁻¹) ^ 2 * (2 ^ d * (2 ^ d * (d : ℝ) ^ 2)) := by
        gcongr
    _ = 1 := by field_simp; ring
