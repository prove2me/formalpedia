-- Prove2me | solution 1 for SecretaryWD.KnownOpt.known_opt_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:19:58.897398+00:00
-- url     : https://prove2.me/submissions/1a7be781-758b-40a6-a1f4-853654b7e658

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

set_option autoImplicit false

lemma pba8_fiber {n : ℕ} (i j : Fin n) :
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

lemma pba8_avg {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
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
theorem pba8_good_pairs {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
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
    simp only [pba8_avg]
    have hfib : ∀ i j : Fin n,
        ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i = j)).card : ℝ)
          = (n.factorial : ℝ) / n := by
      intro i j
      rw [eq_div_iff hnpos.ne']
      exact pba8_fiber i j
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
theorem pba8_notacc {n : ℕ} [NeZero n] (d v : Fin n → ℝ) (Z : ℝ)
    (π : Equiv.Perm (Fin n)) (hπ : π ∈ Finset.univ \ acceptingPerms d v Z) (k : Fin n) :
    d k * v (π k) < Z / 2 := by
  have h1 : π ∉ acceptingPerms d v Z := (Finset.mem_sdiff.1 hπ).2
  have h2 : ¬ Z / 2 ≤ optValue d v π := fun h =>
    h1 (by unfold acceptingPerms; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have h3 : optValue d v π < Z / 2 := not_le.1 h2
  unfold optValue at h3
  exact (Finset.sup'_lt_iff _).1 h3 k (Finset.mem_univ _)

open SecretaryWD.KnownOpt in
theorem pba8_card {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (i j : Fin n)
    (hij : Z / 2 ≤ d i * v j) :
    (Finset.univ \ acceptingPerms d v Z).card ≤ n * (goodPerms d v Z i j).card ∧
      (2 * (acceptingPerms d v Z).card ≤ n.factorial →
        n.factorial ≤ 2 * n * (goodPerms d v Z i j).card) := by
  have part1 : (Finset.univ \ acceptingPerms d v Z).card ≤ n * (goodPerms d v Z i j).card := by
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := fun π : Equiv.Perm (Fin n) => π * Equiv.swap i (π.symm j)) ?_ n ?_
    · intro π hπ
      have hna := pba8_notacc d v Z π hπ
      unfold goodPerms
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
      intro k hk
      unfold discProd
      rw [Equiv.Perm.mul_apply]
      have hki : k ≠ i := ne_of_lt hk
      by_cases hkm : k = π.symm j
      · subst hkm
        rw [Equiv.swap_apply_right]
        have h1 : d (π.symm j) * v j < Z / 2 := by
          have := hna (π.symm j); rwa [Equiv.apply_symm_apply] at this
        have hlt : d (π.symm j) * v j < d i * v j := lt_of_lt_of_le h1 hij
        have hvj : 0 < v j := by
          by_contra hcon
          have : v j = 0 := le_antisymm (not_lt.mp hcon) (hv j)
          rw [this, mul_zero, mul_zero] at hlt; exact lt_irrefl _ hlt
        have hdle : d (π.symm j) ≤ d i := le_of_lt (lt_of_mul_lt_mul_right hlt hvj.le)
        calc d (π.symm j) * v (π i) ≤ d i * v (π i) :=
              mul_le_mul_of_nonneg_right hdle (hv _)
          _ < Z / 2 := hna i
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkm]
        exact hna k
    · intro σ _
      calc (Finset.filter (fun π : Equiv.Perm (Fin n) => π * Equiv.swap i (π.symm j) = σ)
              (Finset.univ \ acceptingPerms d v Z)).card
          ≤ (Finset.univ.image (fun m : Fin n => σ * Equiv.swap i m)).card := by
            apply Finset.card_le_card
            intro π hπ
            simp only [Finset.mem_filter] at hπ
            simp only [Finset.mem_image, Finset.mem_univ, true_and]
            refine ⟨π.symm j, ?_⟩
            rw [← hπ.2, mul_assoc, Equiv.swap_mul_self, mul_one]
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = n := by simp
  refine ⟨part1, fun h2 => ?_⟩
  have hsplit : (Finset.univ \ acceptingPerms d v Z).card + (acceptingPerms d v Z).card
      = n.factorial := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
  calc n.factorial ≤ 2 * (Finset.univ \ acceptingPerms d v Z).card := by omega
    _ ≤ 2 * (n * (goodPerms d v Z i j).card) := Nat.mul_le_mul_left 2 part1
    _ = 2 * n * (goodPerms d v Z i j).card := by ring

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
    have hS := pba8_good_pairs d v hd hv Z hZ
    rw [pba8_eq_good_sum d v Z]
    have hterm : ∀ i : Fin n, ∀ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        1 / 2 * ((1 / (n : ℝ)) * (d i * v j))
          ≤ d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ)) := by
      intro i j hj
      have hij : Z / 2 ≤ d i * v j := (Finset.mem_filter.1 hj).2
      have hc := (pba8_card d v hd hv Z i j hij).2 hA
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
