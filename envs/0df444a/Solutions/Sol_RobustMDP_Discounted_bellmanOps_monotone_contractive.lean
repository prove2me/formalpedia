-- Prove2me | solution 1 for RobustMDP.Discounted.bellmanOps_monotone_contractive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:43:54.642263+00:00
-- url     : https://prove2.me/submissions/a0fdbe0d-425d-4389-b6d5-15c6cd48528d

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

lemma aux_bmc_bdd {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S ⊆ stdSimplex ℝ (Fin n))
    (v : Fin n → ℝ) :
    BddAbove ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S) := by
  refine ⟨∑ j, |v j|, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' := hS hp
  apply Finset.sum_le_sum
  intro j _
  have h0 := hp'.1 j
  have h1 : p j ≤ 1 := by
    calc p j ≤ ∑ k, p k := Finset.single_le_sum (fun k _ => hp'.1 k) (Finset.mem_univ j)
      _ = 1 := hp'.2
  calc p j * v j ≤ p j * |v j| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ 1 * |v j| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |v j| := one_mul _

lemma aux_bmc_le {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) (u v : Fin n → ℝ) (c : ℝ)
    (h : ∀ p ∈ S, ∑ j, p j * u j ≤ ∑ j, p j * v j + c) :
    Shared.supportFunction S u ≤ Shared.supportFunction S v + c := by
  unfold Shared.supportFunction
  apply csSup_le (hne.image _)
  rintro _ ⟨p, hp, rfl⟩
  have h2 : ∑ j, p j * v j ≤ sSup ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S) :=
    le_csSup (aux_bmc_bdd hS v) (Set.mem_image_of_mem _ hp)
  have h3 := h p hp
  show ∑ j, p j * u j ≤ _
  linarith

lemma aux_bmc_mono {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) {u v : Fin n → ℝ} (huv : u ≤ v) :
    Shared.supportFunction S u ≤ Shared.supportFunction S v := by
  have := aux_bmc_le hS hne u v 0 (by
    intro p hp
    rw [add_zero]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (huv j) ((hS hp).1 j))
  linarith

lemma aux_bmc_lip_half {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) (u v : Fin n → ℝ) :
    Shared.supportFunction S u ≤ Shared.supportFunction S v + dist u v := by
  apply aux_bmc_le hS hne
  intro p hp
  have hp' := hS hp
  have hj : ∀ j, u j ≤ v j + dist u v := by
    intro j
    have h1 := dist_le_pi_dist u v j
    rw [Real.dist_eq] at h1
    have := (abs_sub_le_iff.1 h1).1
    linarith
  calc ∑ j, p j * u j ≤ ∑ j, (p j * v j + p j * dist u v) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hj j) (hp'.1 j)
    _ = ∑ j, p j * v j + (∑ j, p j) * dist u v := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ j, p j * v j + dist u v := by rw [hp'.2, one_mul]

lemma aux_bmc_lip {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) (u v : Fin n → ℝ) :
    |Shared.supportFunction S u - Shared.supportFunction S v| ≤ dist u v := by
  have h1 := aux_bmc_lip_half hS hne u v
  have h2 := aux_bmc_lip_half hS hne v u
  rw [dist_comm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

end RobustMDP.Discounted

open RobustMDP.Discounted

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) :
    (Monotone M.bellmanOp ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ M.bellmanOp) ∧
    ∀ π : StationaryPolicy n A,
      Monotone (M.policyOp π) ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ (M.policyOp π) := by
  have hν := M.discount_nonneg
  refine ⟨⟨?_, ?_⟩, fun π => ⟨?_, ?_⟩⟩
  · intro u v huv i
    unfold Model.bellmanOp
    apply Finset.le_inf'
    intro a _
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ a)) ?_
    have := aux_bmc_mono (M.rows_subset_simplex a i) (M.rows_nonempty a i) huv
    have := mul_le_mul_of_nonneg_left this hν
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    show dist _ _ ≤ M.discount * dist u v
    rw [dist_pi_le_iff (mul_nonneg hν dist_nonneg)]
    intro i
    unfold Model.bellmanOp
    rw [Real.dist_eq, abs_sub_le_iff]
    have key : ∀ x y : Fin n → ℝ,
        Finset.univ.inf' Finset.univ_nonempty
          (fun a => M.cost i a + M.discount * RobustMDP.Shared.supportFunction (M.rows a i) x)
        - M.discount * dist x y ≤
        Finset.univ.inf' Finset.univ_nonempty
          (fun a => M.cost i a + M.discount * RobustMDP.Shared.supportFunction (M.rows a i) y) := by
      intro x y
      apply Finset.le_inf'
      intro a _
      have h1 := Finset.inf'_le
        (fun a => M.cost i a + M.discount * RobustMDP.Shared.supportFunction (M.rows a i) x)
        (Finset.mem_univ a)
      have h2 := aux_bmc_lip_half (M.rows_subset_simplex a i) (M.rows_nonempty a i) x y
      have h3 := mul_le_mul_of_nonneg_left h2 hν
      show _ ≤ M.cost i a + M.discount * RobustMDP.Shared.supportFunction (M.rows a i) y
      nlinarith [h1, h3]
    have k1 := key u v
    have k2 := key v u
    rw [dist_comm] at k2
    constructor <;> linarith
  · intro u v huv i
    unfold Model.policyOp
    have := aux_bmc_mono (M.rows_subset_simplex (π i) i) (M.rows_nonempty (π i) i) huv
    have := mul_le_mul_of_nonneg_left this hν
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    show dist _ _ ≤ M.discount * dist u v
    rw [dist_pi_le_iff (mul_nonneg hν dist_nonneg)]
    intro i
    unfold Model.policyOp
    rw [Real.dist_eq]
    have h := aux_bmc_lip (M.rows_subset_simplex (π i) i) (M.rows_nonempty (π i) i) u v
    have : M.cost i (π i) + M.discount * RobustMDP.Shared.supportFunction (M.rows (π i) i) u -
        (M.cost i (π i) + M.discount * RobustMDP.Shared.supportFunction (M.rows (π i) i) v) =
        M.discount * (RobustMDP.Shared.supportFunction (M.rows (π i) i) u -
          RobustMDP.Shared.supportFunction (M.rows (π i) i) v) := by ring
    rw [this, abs_mul, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left h hν
