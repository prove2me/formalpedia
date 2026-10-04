-- Prove2me | solution 1 for SecretaryWD.KnownOpt.expectedAlg_eq_good_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:51:28.612443+00:00
-- url     : https://prove2.me/submissions/eb5b5ef5-aa6b-4e11-8489-11ee47621844

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

set_option autoImplicit false

open SecretaryWD.KnownOpt in
lemma p93707905_perm {n : ℕ} (d v : Fin n → ℝ) (Z : ℝ) (π : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n,
      if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
      then d i * v j * (1 / (n.factorial : ℝ)) else 0)
      = (1 / (n.factorial : ℝ)) * algValue d v Z π := by
  have hinner : ∀ i : Fin n, (∑ j : Fin n,
      if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
      then d i * v j * (1 / (n.factorial : ℝ)) else 0) =
      if (Z / 2 ≤ discProd d v π i ∧ ∀ k, k < i → ¬ (Z / 2 ≤ discProd d v π k))
      then discProd d v π i * (1 / (n.factorial : ℝ)) else 0 := by
    intro i
    rw [Finset.sum_eq_single (π i)]
    · unfold discProd
      simp only [true_and, not_le]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨_, h, _⟩
      exact hb h.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hinner]
  unfold algValue selectTime
  by_cases h : ∃ j, Z / 2 ≤ discProd d v π j
  · rw [dif_pos h]
    simp only
    rw [Finset.sum_eq_single (Fin.find (fun j => Z / 2 ≤ discProd d v π j) h)]
    · rw [if_pos ((Fin.find_eq_iff h).1 rfl)]
      ring
    · intro b _ hb
      rw [if_neg]
      intro hc
      exact hb ((Fin.find_eq_iff h).2 hc).symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [dif_neg h]
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    rintro ⟨hi, _⟩
    exact h ⟨i, hi⟩

open SecretaryWD.KnownOpt in
theorem solution {n : ℕ} (d v : Fin n → ℝ) (Z : ℝ) :
    expectedAlg d v Z =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ)) := by
  have hR : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ))) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ π : Equiv.Perm (Fin n),
        if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
        then d i * v j * (1 / (n.factorial : ℝ)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : Z / 2 ≤ d i * v j
    · rw [if_pos hz]
      simp only [hz, true_and]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      unfold goodPerms
      ring
    · rw [if_neg hz]
      simp only [hz, false_and, if_false, Finset.sum_const_zero]
  rw [hR]
  unfold expectedAlg
  symm
  calc (∑ i : Fin n, ∑ j : Fin n, ∑ π : Equiv.Perm (Fin n),
        if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
        then d i * v j * (1 / (n.factorial : ℝ)) else 0)
      = ∑ i : Fin n, ∑ π : Equiv.Perm (Fin n), ∑ j : Fin n,
        if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
        then d i * v j * (1 / (n.factorial : ℝ)) else 0 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ π : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ j : Fin n,
        if (Z / 2 ≤ d i * v j ∧ (π i = j ∧ ∀ k, k < i → discProd d v π k < Z / 2))
        then d i * v j * (1 / (n.factorial : ℝ)) else 0 := Finset.sum_comm
    _ = ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * algValue d v Z π :=
        Finset.sum_congr rfl (fun π _ => p93707905_perm d v Z π)
