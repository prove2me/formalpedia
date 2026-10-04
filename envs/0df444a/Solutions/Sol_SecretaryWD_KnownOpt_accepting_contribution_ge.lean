-- Prove2me | solution 1 for SecretaryWD.KnownOpt.accepting_contribution_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:42:22.39519+00:00
-- url     : https://prove2.me/submissions/bd8cb66d-6970-452f-87ea-7f7d1240e526

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

open SecretaryWD.KnownOpt Finset in
theorem solution {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 2 ≤ acceptingContribution d v Z := by
  have hopt : ∀ π : Equiv.Perm (Fin n), 0 ≤ optValue d v π := fun π =>
    le_trans (mul_nonneg (hd 0) (hv (π 0)))
      (Finset.le_sup' (discProd d v π) (Finset.mem_univ (0 : Fin n)))
  have hc : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rcases le_or_gt 0 Z with hZ0 | hZ0
  · have hsplit : expectedOPT d v = acceptingContribution d v Z +
        ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ¬ Z / 2 ≤ optValue d v π), (1 / (n.factorial : ℝ)) * optValue d v π := by
      unfold expectedOPT acceptingContribution acceptingPerms
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hR : ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ¬ Z / 2 ≤ optValue d v π), (1 / (n.factorial : ℝ)) * optValue d v π
        ≤ ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ¬ Z / 2 ≤ optValue d v π), (1 / (n.factorial : ℝ)) * (Z / 2) := by
      apply Finset.sum_le_sum
      intro π hπ
      have h1 := (Finset.mem_filter.1 hπ).2
      have h2 : (0 : ℝ) ≤ 1 / (n.factorial : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (le_of_lt (not_le.1 h1)) h2
    have hR2 : ∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ¬ Z / 2 ≤ optValue d v π), (1 / (n.factorial : ℝ)) * (Z / 2)
        ≤ ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * (Z / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have hfull : ∑ π : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) * (Z / 2) = Z / 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    linarith
  · have : 0 ≤ acceptingContribution d v Z :=
      Finset.sum_nonneg (fun π _ => mul_nonneg (by positivity) (hopt π))
    linarith
