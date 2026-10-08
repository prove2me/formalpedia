-- Prove2me | solution 1 for RevenueManagement.dynamic_optimal_controls_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:47:34.017798+00:00
-- url     : https://prove2.me/submissions/4eba738d-ed73-441d-83b5-59f2a671e09b

import Mathlib
import Definitions.Def_RevenueManagement_singleResource_v2

set_option autoImplicit false

namespace RMDynAux76
open RevenueManagement

/-- Expected one-period gain term used in the dynamic recursion. -/
noncomputable def E (s : Finset ℕ) (w : ℕ → ℝ) (r : ℕ → ℝ) (d : ℝ) : ℝ :=
  ∑ j ∈ s, w j * max (r j - d) 0 + (1 - ∑ j ∈ s, w j) * max (0 - d) 0

lemma go_zero (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k : ℕ) :
    dynValueGo lam p n T k 0 = 0 := by
  cases k <;> simp [dynValueGo]

lemma go_succ (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k y : ℕ) :
    dynValueGo lam p n T (k + 1) (y + 1) = dynValueGo lam p n T k (y + 1) +
      E (Finset.Icc 1 n) (fun j => lam j (T - k)) p
        (dynValueGo lam p n T k (y + 1) - dynValueGo lam p n T k y) := by
  simp only [dynValueGo, E]

lemma pw1 (a b c R : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ (b + max (R - b) 0 - max (R - c) 0) - (a + max (R - a) 0 - max (R - b) 0) := by
  simp only [max_def]; split_ifs <;> linarith

lemma pw0 (a b R : ℝ) (hab : a ≤ b) :
    0 ≤ (b + max (R - b) 0) - (a + max (R - a) 0 - max (R - b) 0) := by
  simp only [max_def]; split_ifs <;> linarith

lemma E_diff (s : Finset ℕ) (w r : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hS : ∑ j ∈ s, w j ≤ 1)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    a + E s w r a - E s w r b ≤ b + E s w r b - E s w r c := by
  unfold E
  have h1 : 0 ≤ ∑ j ∈ s, w j * ((b + max (r j - b) 0 - max (r j - c) 0) -
      (a + max (r j - a) 0 - max (r j - b) 0)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (pw1 a b c (r j) hab hbc)
  have h2 : 0 ≤ (1 - ∑ j ∈ s, w j) * ((b + max (0 - b) 0 - max (0 - c) 0) -
      (a + max (0 - a) 0 - max (0 - b) 0)) :=
    mul_nonneg (by linarith) (pw1 a b c 0 hab hbc)
  have e : ∑ j ∈ s, w j * ((b + max (r j - b) 0 - max (r j - c) 0) -
      (a + max (r j - a) 0 - max (r j - b) 0)) =
      (b - a) * ∑ j ∈ s, w j + 2 * ∑ j ∈ s, w j * max (r j - b) 0
        - ∑ j ∈ s, w j * max (r j - c) 0 - ∑ j ∈ s, w j * max (r j - a) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  nlinarith [h1, h2, e]

lemma E_diff0 (s : Finset ℕ) (w r : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (hS : ∑ j ∈ s, w j ≤ 1)
    (a b : ℝ) (hab : a ≤ b) :
    a + E s w r a - E s w r b ≤ b + E s w r b := by
  unfold E
  have h1 : 0 ≤ ∑ j ∈ s, w j * ((b + max (r j - b) 0) -
      (a + max (r j - a) 0 - max (r j - b) 0)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (pw0 a b (r j) hab)
  have h2 : 0 ≤ (1 - ∑ j ∈ s, w j) * ((b + max (0 - b) 0) -
      (a + max (0 - a) 0 - max (0 - b) 0)) :=
    mul_nonneg (by linarith) (pw0 a b 0 hab)
  have e : ∑ j ∈ s, w j * ((b + max (r j - b) 0) -
      (a + max (r j - a) 0 - max (r j - b) 0)) =
      (b - a) * ∑ j ∈ s, w j + 2 * ∑ j ∈ s, w j * max (r j - b) 0
        - ∑ j ∈ s, w j * max (r j - a) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  nlinarith [h1, h2, e]

lemma go_step (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) :
    ∀ k x, 1 ≤ x →
      dynValueGo lam p n T k (x + 1) - dynValueGo lam p n T k x ≤
        dynValueGo lam p n T k x - dynValueGo lam p n T k (x - 1) := by
  intro k
  induction k with
  | zero => intro x _; simp [dynValueGo]
  | succ k ih =>
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have hw : ∀ j, 0 ≤ (fun j => lam j (T - k)) j := fun j => hlam.1 j _
    have hS : ∑ j ∈ Finset.Icc 1 n, (fun j => lam j (T - k)) j ≤ 1 := hlam.2 _
    have hab := ih (y + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hab ⊢
    rw [go_succ lam p n T k (y + 1), go_succ lam p n T k y]
    rcases y with _ | z
    · rw [go_zero] at hab ⊢
      have := E_diff0 (Finset.Icc 1 n) (fun j => lam j (T - k)) p hw hS
        (dynValueGo lam p n T k (0 + 1 + 1) - dynValueGo lam p n T k (0 + 1))
        (dynValueGo lam p n T k (0 + 1) - 0) hab
      simp only [sub_zero] at this ⊢
      have h0 := go_zero lam p n T (k + 1)
      linarith
    · have hbc := ih (z + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hbc
      rw [go_succ lam p n T k z]
      have := E_diff (Finset.Icc 1 n) (fun j => lam j (T - k)) p hw hS
        (dynValueGo lam p n T k (z + 1 + 1 + 1) - dynValueGo lam p n T k (z + 1 + 1))
        (dynValueGo lam p n T k (z + 1 + 1) - dynValueGo lam p n T k (z + 1))
        (dynValueGo lam p n T k (z + 1) - dynValueGo lam p n T k z) hab hbc
      linarith

lemma go_anti (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) (k : ℕ) :
    ∀ x y, 1 ≤ x → x ≤ y →
      dynValueGo lam p n T k y - dynValueGo lam p n T k (y - 1) ≤
        dynValueGo lam p n T k x - dynValueGo lam p n T k (x - 1) := by
  intro x y hx hxy
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hy ih =>
    have := go_step lam p n T hlam k y (by omega)
    simp only [Nat.add_sub_cancel]
    linarith

lemma delta_anti (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T s : ℕ) (hlam : IsArrivalModel lam n)
    (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    dynDelta lam p n T s y ≤ dynDelta lam p n T s x := by
  unfold dynDelta dynValue
  exact go_anti lam p n T hlam _ x y hx hxy

lemma le_sup_aux (C x : ℕ) (P : ℕ → Prop) {dec : DecidablePred P} (hx : x < C + 1) (hP : P x) :
    x ≤ ((Finset.range (C + 1)).filter P).sup id :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, hP⟩)

lemma sup_mem_aux (C : ℕ) (P : ℕ → Prop) {dec : DecidablePred P}
    (h : 1 ≤ ((Finset.range (C + 1)).filter P).sup id) :
    ∃ z, z < C + 1 ∧ P z ∧ ((Finset.range (C + 1)).filter P).sup id = z := by
  have hne : ((Finset.range (C + 1)).filter P).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at h
    simp at h
  obtain ⟨z, hz, hzeq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_filter, Finset.mem_range] at hz
  exact ⟨z, hz.1, hz.2, hzeq⟩

lemma sup_mono_aux (C : ℕ) (P Q : ℕ → Prop) {dP : DecidablePred P} {dQ : DecidablePred Q}
    (h : ∀ x, P x → Q x) :
    ((Finset.range (C + 1)).filter P).sup id ≤ ((Finset.range (C + 1)).filter Q).sup id := by
  apply Finset.sup_le
  intro x hx
  rw [Finset.mem_filter, Finset.mem_range] at hx
  exact le_sup_aux C x Q hx.1 (h x hx.2)

lemma opt_one (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x j : ℕ)
    (h : dynDelta lam p n T (t + 1) x ≤ p j) : IsDynOptimal lam p n T t x j 1 := by
  refine ⟨le_rfl, fun u' hu' => ?_⟩
  interval_cases u' <;> simp <;> linarith

lemma opt_zero (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x j : ℕ)
    (h : p j ≤ dynDelta lam p n T (t + 1) x) : IsDynOptimal lam p n T t x j 0 := by
  refine ⟨by norm_num, fun u' hu' => ?_⟩
  interval_cases u' <;> simp <;> linarith

lemma prot_opt (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C t : ℕ) (hlam : IsArrivalModel lam n)
    (j x : ℕ) (hj : 1 ≤ j) (hx : 1 ≤ x) (hxC : x ≤ C) :
    IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0) := by
  have hj' : j - 1 + 1 = j := by omega
  split_ifs with hlt
  · apply opt_one
    by_contra hc
    push_neg at hc
    have : x ≤ dynProtLevel lam p n T C t (j - 1) := by
      unfold dynProtLevel
      exact le_sup_aux C x _ (by omega) ⟨hx, by rw [hj']; exact hc⟩
    omega
  · apply opt_zero
    push_neg at hlt
    have h1 : 1 ≤ dynProtLevel lam p n T C t (j - 1) := le_trans hx hlt
    unfold dynProtLevel at h1 hlt
    obtain ⟨z, hzC, ⟨hz1, hzp⟩, hzeq⟩ := sup_mem_aux C _ h1
    rw [hzeq] at hlt
    rw [hj'] at hzp
    have := delta_anti lam p n T (t + 1) hlam x z hx hlt
    linarith

end RMDynAux76

open RevenueManagement in
theorem solution (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) :
    (∀ j, dynProtLevel lam p n T C t j ≤ dynProtLevel lam p n T C t (j + 1)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if C - x < dynBookLimit lam p n T C t j then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynBidPrice lam p n T (t + 1) x ≤ p j then 1 else 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    unfold dynProtLevel
    apply RMDynAux76.sup_mono_aux
    rintro x ⟨hx1, hx⟩
    exact ⟨hx1, lt_of_le_of_lt (hanti (by omega : j + 1 ≤ j + 1 + 1)) hx⟩
  · intro j x hj _ hx hxC
    exact RMDynAux76.prot_opt lam p n T C t hlam j x hj hx hxC
  · intro j x hj _ hx hxC
    have hyC : dynProtLevel lam p n T C t (j - 1) ≤ C := by
      unfold dynProtLevel
      apply Finset.sup_le
      intro z hz
      rw [Finset.mem_filter, Finset.mem_range] at hz
      exact Nat.lt_succ_iff.1 hz.1
    have hiff : (C - x < dynBookLimit lam p n T C t j) ↔
        (dynProtLevel lam p n T C t (j - 1) < x) := by
      unfold dynBookLimit
      omega
    have := RMDynAux76.prot_opt lam p n T C t hlam j x hj hx hxC
    simp only [hiff]
    exact this
  · intro j x _ _ _ _
    unfold dynBidPrice
    split_ifs with h
    · exact RMDynAux76.opt_one lam p n T t x j h
    · exact RMDynAux76.opt_zero lam p n T t x j (le_of_lt (not_le.1 h))
