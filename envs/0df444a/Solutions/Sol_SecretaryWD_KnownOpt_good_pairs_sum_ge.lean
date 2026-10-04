-- Prove2me | solution 1 for SecretaryWD.KnownOpt.good_pairs_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:44:18.83824+00:00
-- url     : https://prove2.me/submissions/5c69ce91-04ed-4428-b8c8-7f858561076a

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

set_option autoImplicit false

lemma pef25_fiber {n : ℕ} (i j : Fin n) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card : ℝ) * n
      = (n.factorial : ℝ) := by
  have hc : ∀ j : Fin n, (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card
      = (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = i)).card := by
    intro j
    apply Finset.card_nbij' (fun π => Equiv.swap i j * π) (fun π => Equiv.swap i j * π)
    · intro π hπ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
      rw [Equiv.Perm.mul_apply, hπ, Equiv.swap_apply_right]
    · intro π hπ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
      rw [Equiv.Perm.mul_apply, hπ, Equiv.swap_apply_left]
    · intro π _
      simp only [← mul_assoc, Equiv.swap_mul_self, one_mul]
    · intro π _
      simp only [← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hsum : (Finset.univ : Finset (Equiv.Perm (Fin n))).card
      = ∑ j : Fin n, (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun π _ => Finset.mem_univ (π i))
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [hc j, hsum]
  push_cast
  ring

lemma pef25_avg {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    ∑ π : Equiv.Perm (Fin n), g (π i)
      = ∑ j : Fin n, ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card : ℝ)
          * g j := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Equiv.Perm (Fin n))) (fun π => π i)
    (fun π => g (π i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_congr rfl (g := fun _ => g j)]
  · rw [Finset.sum_const, nsmul_eq_mul]
  · intro π hπ
    simp only [Finset.mem_filter] at hπ
    rw [hπ.2]

open SecretaryWD.KnownOpt in
theorem solution {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 2 ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
      (1 / (n : ℝ)) * (d i * v j) := by
  set G : Fin n → Fin n → ℝ := fun i j => if Z / 2 ≤ d i * v j then d i * v j else 0 with hG
  have hGnn : ∀ i j, 0 ≤ G i j := by
    intro i j
    simp only [hG]
    split_ifs
    · exact mul_nonneg (hd i) (hv j)
    · exact le_refl 0
  have hnpos : (0 : ℝ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hS : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
      (1 / (n : ℝ)) * (d i * v j)) = ∑ i : Fin n, ∑ j : Fin n, (1 / (n : ℝ)) * G i j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hG]
    split_ifs <;> simp
  rw [hS]
  by_cases hZ0 : Z < 0
  · have : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (1 / (n : ℝ)) * G i j :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (by positivity) (hGnn i j)))
    linarith
  push_neg at hZ0
  have hopt : ∀ π : Equiv.Perm (Fin n), optValue d v π ≤ Z / 2 + ∑ i : Fin n, G i (π i) := by
    intro π
    obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n))
      (discProd d v π)
    have hsumnn : 0 ≤ ∑ i : Fin n, G i (π i) := Finset.sum_nonneg (fun i _ => hGnn i (π i))
    unfold optValue
    rw [hi0]
    unfold discProd
    by_cases hg : Z / 2 ≤ d i0 * v (π i0)
    · have h1 : G i0 (π i0) = d i0 * v (π i0) := by simp only [hG]; rw [if_pos hg]
      have h2 : G i0 (π i0) ≤ ∑ i : Fin n, G i (π i) :=
        Finset.single_le_sum (f := fun i => G i (π i)) (fun i _ => hGnn i (π i))
          (Finset.mem_univ i0)
      linarith
    · push_neg at hg
      linarith
  have hE : expectedOPT d v ≤ ∑ π : Equiv.Perm (Fin n),
      (1 / (n.factorial : ℝ)) * (Z / 2 + ∑ i : Fin n, G i (π i)) := by
    unfold expectedOPT
    apply Finset.sum_le_sum
    intro π _
    exact mul_le_mul_of_nonneg_left (hopt π) (by positivity)
  have hR : (∑ π : Equiv.Perm (Fin n),
      (1 / (n.factorial : ℝ)) * (Z / 2 + ∑ i : Fin n, G i (π i)))
      = Z / 2 + ∑ i : Fin n, ∑ j : Fin n, (1 / (n : ℝ)) * G i j := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Finset.sum_comm]
    simp only [pef25_avg]
    have hfib : ∀ i j : Fin n,
        ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card : ℝ)
          = (n.factorial : ℝ) / n := by
      intro i j
      rw [eq_div_iff hnpos.ne']
      exact pef25_fiber i j
    simp only [hfib]
    rw [mul_add]
    congr 1
    · field_simp
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
  linarith
