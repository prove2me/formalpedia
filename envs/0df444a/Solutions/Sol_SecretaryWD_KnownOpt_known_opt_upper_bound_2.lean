-- Prove2me | solution 2 for SecretaryWD.KnownOpt.known_opt_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:25.693838+00:00
-- url     : https://prove2.me/submissions/eb0e6baa-8ab4-45e7-90b5-9c2a99a9ea3b

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model
import Theorems.Thm_SecretaryWD_KnownOpt_good_perms_card_ge
import Theorems.Thm_SecretaryWD_KnownOpt_good_pairs_sum_ge

-- carved verbatim out of submission 1a7be781-758b-40a6-a1f4-853654b7e658, lines 293-351

section
set_option autoImplicit false

open SecretaryWD.KnownOpt in
lemma pba8_perm {n : ℕ} (d v : Fin n → ℝ) (Z : ℝ) (π : Equiv.Perm (Fin n)) :
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
theorem pba8_eq_good_sum {n : ℕ} (d v : Fin n → ℝ) (Z : ℝ) :
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
        Finset.sum_congr rfl (fun π _ => pba8_perm d v Z π)

open SecretaryWD.KnownOpt in
lemma pba8_alg_nonneg {n : ℕ} (d v : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e)
    (Z : ℝ) (π : Equiv.Perm (Fin n)) : 0 ≤ algValue d v Z π := by
  unfold algValue
  cases selectTime d v Z π with
  | none => exact le_refl 0
  | some j => exact mul_nonneg (hd j) (hv (π j))

open SecretaryWD.KnownOpt in
lemma pba8_alg_acc {n : ℕ} [NeZero n] (d v : Fin n → ℝ) (Z : ℝ) (π : Equiv.Perm (Fin n))
    (hπ : π ∈ acceptingPerms d v Z) : Z / 2 ≤ algValue d v Z π := by
  simp only [acceptingPerms, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n))
      (discProd d v π)
  have h : ∃ j, Z / 2 ≤ discProd d v π j := ⟨i0, by unfold optValue at hπ; rwa [hi0] at hπ⟩
  unfold algValue selectTime
  rw [dif_pos h]
  exact ((Fin.find_eq_iff h).1 rfl).1

open SecretaryWD.KnownOpt in
theorem solution {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 4 ≤ expectedAlg d v Z := by
  have hN : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hEnn : 0 ≤ expectedAlg d v Z :=
    Finset.sum_nonneg (fun π _ => mul_nonneg (by positivity) (pba8_alg_nonneg d v hd hv Z π))
  rcases le_or_gt Z 0 with hZ0 | hZ0
  · linarith
  by_cases hA : n.factorial < 2 * (acceptingPerms d v Z).card
  · have h1 : ∑ π ∈ acceptingPerms d v Z, (1 / (n.factorial : ℝ)) * (Z / 2)
        ≤ expectedAlg d v Z := by
      unfold expectedAlg
      calc ∑ π ∈ acceptingPerms d v Z, (1 / (n.factorial : ℝ)) * (Z / 2)
          ≤ ∑ π ∈ acceptingPerms d v Z, (1 / (n.factorial : ℝ)) * algValue d v Z π :=
            Finset.sum_le_sum (fun π hπ =>
              mul_le_mul_of_nonneg_left (pba8_alg_acc d v Z π hπ) (by positivity))
        _ ≤ ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * algValue d v Z π :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun π _ _ => mul_nonneg (by positivity) (pba8_alg_nonneg d v hd hv Z π))
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hA' : (n.factorial : ℝ) ≤ 2 * ((acceptingPerms d v Z).card : ℝ) := by
      exact_mod_cast hA.le
    have h2 : Z / 4 ≤ ((acceptingPerms d v Z).card : ℝ) * (1 / (n.factorial : ℝ) * (Z / 2)) := by
      rw [show ((acceptingPerms d v Z).card : ℝ) * (1 / (n.factorial : ℝ) * (Z / 2))
          = ((acceptingPerms d v Z).card : ℝ) * Z / (2 * (n.factorial : ℝ)) by
            field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  · push_neg at hA
    have hS := SecretaryWD.KnownOpt.good_pairs_sum_ge d v hd hv Z hZ
    rw [pba8_eq_good_sum d v Z]
    have hterm : ∀ i : Fin n, ∀ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        1 / 2 * ((1 / (n : ℝ)) * (d i * v j))
          ≤ d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ)) := by
      intro i j hj
      have hij : Z / 2 ≤ d i * v j := (Finset.mem_filter.1 hj).2
      have hc := (SecretaryWD.KnownOpt.good_perms_card_ge d v hd hv Z i j hij).2 hA
      have hc' : (n.factorial : ℝ) ≤ 2 * (n : ℝ) * ((goodPerms d v Z i j).card : ℝ) := by
        exact_mod_cast hc
      have hx : 0 ≤ d i * v j := mul_nonneg (hd i) (hv j)
      have hq : 1 / (2 * (n : ℝ)) ≤ ((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hN]
        linarith
      calc 1 / 2 * ((1 / (n : ℝ)) * (d i * v j)) = d i * v j * (1 / (2 * (n : ℝ))) := by ring
        _ ≤ d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hq hx
    have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => Finset.sum_le_sum (hterm i))
    have he : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        1 / 2 * ((1 / (n : ℝ)) * (d i * v j))) = 1 / 2 * ∑ i : Fin n,
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
            (1 / (n : ℝ)) * (d i * v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    linarith

end
