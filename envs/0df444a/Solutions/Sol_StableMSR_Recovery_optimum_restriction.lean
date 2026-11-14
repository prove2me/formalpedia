-- Prove2me | solution 1 for StableMSR.Recovery.optimum_restriction
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T13:39:49.414455+00:00
-- url     : https://prove2.me/submissions/d591adc0-80c9-4216-827e-381e81c3d2e4

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

private lemma member_subset_of_feasible {n k : ℕ} {W : Cluster n} {Q : Partition n}
    (hQ : Feasible W k Q) {C : Cluster n} (hC : C ∈ Q) : C ⊆ W := by
  intro x hx
  rw [← hQ.2.2.2]
  exact Finset.mem_biUnion.mpr ⟨C, hC, hx⟩

private lemma restriction_union {n k : ℕ} {O : Partition n} {W : Cluster n}
    (hO : Feasible Finset.univ k O) (halign : Aligned O W) :
    (restrictPartition O W).biUnion id = W := by
  classical
  obtain ⟨F, hFO, hFW⟩ := halign
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hC).2 hxC
  · intro x hx
    rw [← hFW] at hx
    obtain ⟨C, hCF, hxC⟩ := Finset.mem_biUnion.mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨C, ?_, hxC⟩
    apply Finset.mem_filter.mpr
    refine ⟨hFO hCF, ?_⟩
    intro y hy
    rw [← hFW]
    exact Finset.mem_biUnion.mpr ⟨C, hCF, hy⟩

private lemma restriction_feasible {n k : ℕ} {O : Partition n} {W : Cluster n}
    (hO : Feasible Finset.univ k O) (halign : Aligned O W) :
    Feasible W (restrictPartition O W).card (restrictPartition O W) := by
  classical
  refine ⟨rfl, ?_, ?_, restriction_union hO halign⟩
  · intro C hC
    exact hO.2.1 C (Finset.mem_filter.mp hC).1
  · intro C hC D hD hCD
    exact hO.2.2.1 (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hCD

private lemma outside_disjoint {n k : ℕ} {O : Partition n} {W : Cluster n}
    (hO : Feasible Finset.univ k O) (halign : Aligned O W)
    {C : Cluster n} (hC : C ∈ O \ restrictPartition O W) : Disjoint C W := by
  classical
  obtain ⟨hCO, hCnR⟩ := Finset.mem_sdiff.mp hC
  apply Finset.disjoint_left.mpr
  intro x hxC hxW
  rw [← restriction_union hO halign] at hxW
  obtain ⟨D, hDR, hxD⟩ := Finset.mem_biUnion.mp hxW
  have hCD : C ≠ D := by
    intro h
    apply hCnR
    simpa [h] using hDR
  exact Finset.disjoint_left.mp
    (hO.2.2.1 hCO (Finset.mem_filter.mp hDR).1 hCD) hxC hxD

private lemma replacement_disjoint {n k : ℕ} {O Q : Partition n} {W : Cluster n}
    (hO : Feasible Finset.univ k O) (halign : Aligned O W)
    (hQ : Feasible W (restrictPartition O W).card Q) :
    Disjoint Q (O \ restrictPartition O W) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCQ hCT
  obtain ⟨x, hx⟩ := hQ.2.1 C hCQ
  exact Finset.disjoint_left.mp (outside_disjoint hO halign hCT)
    hx (member_subset_of_feasible hQ hCQ hx)

private lemma replacement_feasible {n k : ℕ} {O Q : Partition n} {W : Cluster n}
    (hO : Feasible Finset.univ k O) (halign : Aligned O W)
    (hQ : Feasible W (restrictPartition O W).card Q) :
    Feasible Finset.univ k (Q ∪ (O \ restrictPartition O W)) := by
  classical
  let R := restrictPartition O W
  let T := O \ R
  have hRsub : R ⊆ O := Finset.filter_subset _ _
  have hRT : R ∪ T = O := Finset.union_sdiff_of_subset hRsub
  have hRTdisj : Disjoint R T := disjoint_sdiff_self_right
  have hQTdisj : Disjoint Q T := replacement_disjoint hO halign hQ
  change Feasible Finset.univ k (Q ∪ T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hQTdisj, hQ.1]
    rw [← Finset.card_union_of_disjoint hRTdisj, hRT]
    exact hO.1
  · intro C hC
    rcases Finset.mem_union.mp hC with hCQ | hCT
    · exact hQ.2.1 C hCQ
    · exact hO.2.1 C (Finset.mem_sdiff.mp hCT).1
  · intro C hC D hD hCD
    rcases Finset.mem_union.mp hC with hCQ | hCT <;>
      rcases Finset.mem_union.mp hD with hDQ | hDT
    · exact hQ.2.2.1 hCQ hDQ hCD
    · exact ((outside_disjoint hO halign hDT).mono_right
        (member_subset_of_feasible hQ hCQ)).symm
    · exact (outside_disjoint hO halign hCT).mono_right
        (member_subset_of_feasible hQ hDQ)
    · exact hO.2.2.1 (Finset.mem_sdiff.mp hCT).1
        (Finset.mem_sdiff.mp hDT).1 hCD
  · rw [Finset.union_biUnion, hQ.2.2.2]
    rw [← restriction_union hO halign, ← Finset.union_biUnion, hRT]
    exact hO.2.2.2

private lemma cost_union_disjoint {n : ℕ} (d : Point n → Point n → ℝ)
    {A B : Partition n} (hAB : Disjoint A B) :
    cost d (A ∪ B) = cost d A + cost d B := by
  classical
  exact Finset.sum_union hAB

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (O : Partition n) (hO : UniqueOptimal d Finset.univ k O)
    (W : Cluster n) (hW : W.Nonempty) (halign : Aligned O W) :
    UniqueOptimal d W (restrictPartition O W).card (restrictPartition O W) := by
  classical
  let R := restrictPartition O W
  let T := O \ R
  have hRsub : R ⊆ O := Finset.filter_subset _ _
  have hRT : R ∪ T = O := Finset.union_sdiff_of_subset hRsub
  have hRTdisj : Disjoint R T := disjoint_sdiff_self_right
  have hcostO : cost d O = cost d R + cost d T := by
    rw [← hRT]
    exact cost_union_disjoint d hRTdisj
  have hRfeas : Feasible W R.card R := restriction_feasible hO.1.1 halign
  have hRopt : Optimal d W R.card R := by
    refine ⟨hRfeas, ?_⟩
    intro Q hQ
    have hExt := replacement_feasible hO.1.1 halign hQ
    have hcost := hO.1.2 (Q ∪ T) hExt
    rw [hcostO, cost_union_disjoint d (replacement_disjoint hO.1.1 halign hQ)] at hcost
    linarith
  refine ⟨hRopt, ?_⟩
  intro Q hQ
  have hExt := replacement_feasible hO.1.1 halign hQ.1
  have hcostQ : cost d Q ≤ cost d R := hQ.2 R hRfeas
  have hExtopt : Optimal d Finset.univ k (Q ∪ T) := by
    refine ⟨hExt, ?_⟩
    intro P hP
    have hbound := hO.1.2 P hP
    rw [cost_union_disjoint d (replacement_disjoint hO.1.1 halign hQ.1)]
    rw [hcostO] at hbound
    linarith
  have hExtEq : Q ∪ T = O := hO.2 (Q ∪ T) hExtopt
  apply Finset.Subset.antisymm
  · intro C hCQ
    apply Finset.mem_filter.mpr
    refine ⟨?_, member_subset_of_feasible hQ.1 hCQ⟩
    rw [← hExtEq]
    exact Finset.mem_union_left T hCQ
  · intro C hCR
    have hCO : C ∈ O := hRsub hCR
    rw [← hExtEq] at hCO
    rcases Finset.mem_union.mp hCO with hCQ | hCT
    · exact hCQ
    · exact False.elim ((Finset.mem_sdiff.mp hCT).2 hCR)
