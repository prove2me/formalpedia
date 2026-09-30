-- Prove2me | solution 1 for UnderstandingML.kmeans_step_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:43:13.633836+00:00
-- url     : https://prove2.me/submissions/119e7f08-0927-430b-a0ed-baa2f4accc07

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML.KMeansAux

/-- The centroid minimizes the within-cluster sum of squared distances. -/
theorem centroid_minimizes {n : ℕ} (C : Finset (UnderstandingML.Vec n))
    (μ : UnderstandingML.Vec n) :
    ∑ x ∈ C, ‖x - UnderstandingML.centroid C‖ ^ 2 ≤ ∑ x ∈ C, ‖x - μ‖ ^ 2 := by
  set c := UnderstandingML.centroid C with hc
  have hsum : ∑ x ∈ C, (x - c) = 0 := by
    rcases C.eq_empty_or_nonempty with h | h
    · simp [h]
    · rw [Finset.sum_sub_distrib, Finset.sum_const, hc, UnderstandingML.centroid]
      have hcard : ((C.card : ℝ) : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hcard, one_smul, sub_self]
  have hexp : ∀ x, ‖x - μ‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * inner ℝ (x - c) (c - μ) + ‖c - μ‖ ^ 2 := by
    intro x
    have : x - μ = (x - c) + (c - μ) := by abel
    rw [this, norm_add_sq_real]
  have hinner : ∑ x ∈ C, inner ℝ (x - c) (c - μ) = 0 := by
    rw [← sum_inner, hsum, inner_zero_left]
  calc ∑ x ∈ C, ‖x - c‖ ^ 2
      ≤ ∑ x ∈ C, ‖x - c‖ ^ 2 + 2 * ∑ x ∈ C, inner ℝ (x - c) (c - μ)
          + ∑ x ∈ C, ‖c - μ‖ ^ 2 := by
        rw [hinner]
        have : 0 ≤ ∑ x ∈ C, ‖c - μ‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
    _ = ∑ x ∈ C, ‖x - μ‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.mul_sum]

/-- Rewriting a double sum over the clusters of a partition as a sum over the points. -/
theorem sum_partition {X : Type*} [DecidableEq X] {k : ℕ} {S : Finset X}
    {C : Fin k → Finset X} (hC : UnderstandingML.IsPartition S C) (g : Fin k → X → ℝ) :
    ∑ i, ∑ x ∈ C i, g i x = ∑ x ∈ S, ∑ i, if x ∈ C i then g i x else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hC.1 i)]

/-- For a point of `S`, the inner sum picks out the cluster containing it. -/
theorem sum_ite_mem {X : Type*} [DecidableEq X] {k : ℕ} {S : Finset X}
    {C : Fin k → Finset X} (hC : UnderstandingML.IsPartition S C) (g : Fin k → X → ℝ)
    {x : X} {i₀ : Fin k} (hx : x ∈ S) (hi₀ : x ∈ C i₀) :
    (∑ i, if x ∈ C i then g i x else 0) = g i₀ x := by
  rw [Finset.sum_eq_single i₀]
  · simp [hi₀]
  · intro i _ hi
    have : x ∉ C i := fun h => hi ((hC.2 x hx).unique h hi₀)
    simp [this]
  · simp

end UnderstandingML.KMeansAux

open UnderstandingML.KMeansAux in
theorem solution {n k : ℕ} (S : Finset (UnderstandingML.Vec n))
    (C C' : Fin k → Finset (UnderstandingML.Vec n))
    (hC : UnderstandingML.IsPartition S C) (hC' : UnderstandingML.IsPartition S C')
    (hnear : UnderstandingML.IsNearestAssignment (fun i ↦ UnderstandingML.centroid (C i)) C') :
    UnderstandingML.kmeansObjective C' ≤ UnderstandingML.kmeansObjective C := by
  classical
  set μ : Fin k → UnderstandingML.Vec n := fun i ↦ UnderstandingML.centroid (C i) with hμ
  -- Step 1: recomputing the centroids of `C'` does not increase the cost
  have step1 : UnderstandingML.kmeansObjective C' ≤ UnderstandingML.centerCost C' μ := by
    unfold UnderstandingML.kmeansObjective UnderstandingML.centerCost
    exact Finset.sum_le_sum fun i _ => centroid_minimizes (C' i) (μ i)
  -- Step 2: reassigning to nearest old centroids does not increase the cost
  have step2 : UnderstandingML.centerCost C' μ ≤ UnderstandingML.centerCost C μ := by
    unfold UnderstandingML.centerCost
    rw [sum_partition hC' (fun i x => ‖x - μ i‖ ^ 2), sum_partition hC (fun i x => ‖x - μ i‖ ^ 2)]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨i', hi', -⟩ := hC'.2 x hx
    obtain ⟨i, hi, -⟩ := hC.2 x hx
    rw [sum_ite_mem hC' (fun i x => ‖x - μ i‖ ^ 2) hx hi',
      sum_ite_mem hC (fun i x => ‖x - μ i‖ ^ 2) hx hi]
    have h := hnear i' x hi' i
    rw [dist_eq_norm, dist_eq_norm] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  exact step1.trans step2
