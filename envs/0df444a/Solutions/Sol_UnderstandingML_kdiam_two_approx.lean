-- Prove2me | solution 1 for UnderstandingML.kdiam_two_approx
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:41:56.025014+00:00
-- url     : https://prove2.me/submissions/1d6e37c9-6872-4bc9-a840-dae271dd87af

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

theorem solution {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ} (μ : Fin k → X)
    (hμ : UnderstandingML.IsFarthestFirst μ) (Chat : Fin k → Finset X)
    (hpart : UnderstandingML.IsPartition Finset.univ Chat)
    (hnear : UnderstandingML.IsNearestAssignment μ Chat) (Cstar : Fin k → Finset X)
    (hstar : UnderstandingML.IsPartition Finset.univ Cstar) (j : Fin k) :
    ∃ j' : Fin k, Metric.diam (↑(Chat j) : Set X) ≤ 2 * Metric.diam (↑(Cstar j') : Set X) := by
  classical
  have hk : (Finset.univ : Finset (Fin k)).Nonempty := ⟨j, Finset.mem_univ _⟩
  have hX : (Finset.univ : Finset X).Nonempty := ⟨μ j, Finset.mem_univ _⟩
  -- distance to the nearest center
  let f : X → ℝ := fun x => Finset.univ.inf' hk (fun i => dist x (μ i))
  -- the farthest-first radius
  let r : ℝ := Finset.univ.sup' hX f
  obtain ⟨xs, -, hxs⟩ := Finset.exists_mem_eq_sup' hX f
  have hr : r = f xs := hxs
  have hf_le : ∀ x i, f x ≤ dist x (μ i) := fun x i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  have hf_r : ∀ x, f x ≤ r := fun x => Finset.le_sup' f (Finset.mem_univ x)
  have hr_nonneg : 0 ≤ r := by
    have := Finset.le_inf' hk (fun i => dist (μ j) (μ i)) (a := 0)
      (fun i _ => dist_nonneg)
    exact this.trans (hf_r (μ j))
  -- upper bound: every cluster of the algorithm has diameter at most `2r`
  have hup : Metric.diam (↑(Chat j) : Set X) ≤ 2 * r := by
    have hball : ∀ x ∈ Chat j, dist x (μ j) ≤ r := by
      intro x hx
      have : dist x (μ j) ≤ f x :=
        Finset.le_inf' hk _ (fun i _ => hnear j x hx i)
      exact this.trans (hf_r x)
    apply Metric.diam_le_of_forall_dist_le (by linarith)
    intro x hx y hy
    calc dist x y ≤ dist x (μ j) + dist (μ j) y := dist_triangle _ _ _
      _ = dist x (μ j) + dist y (μ j) := by rw [dist_comm (μ j) y]
      _ ≤ r + r := add_le_add (hball x hx) (hball y hy)
      _ = 2 * r := by ring
  -- the `k + 1` points `xs, μ 0, …, μ (k-1)` are pairwise at distance at least `r`
  let p : Option (Fin k) → X := fun o => o.elim xs μ
  have hsep_centers : ∀ i i' : Fin k, i' < i → r ≤ dist (μ i) (μ i') := by
    intro i i' hii'
    have hne : Nonempty {i'' : Fin k // i'' < i} := ⟨⟨i', hii'⟩⟩
    have h1 : r ≤ ⨅ i'' : {i'' : Fin k // i'' < i}, dist xs (μ i'') := by
      apply le_ciInf
      intro i''
      rw [hr]
      exact hf_le xs i''
    have h2 : (⨅ i'' : {i'' : Fin k // i'' < i}, dist (μ i) (μ i'')) ≤ dist (μ i) (μ i') := by
      exact ciInf_le (f := fun i'' : {i'' : Fin k // i'' < i} => dist (μ i) (μ i''))
        (Set.finite_range _).bddBelow ⟨i', hii'⟩
    exact h1.trans ((hμ i xs).trans h2)
  have hsep : ∀ o o' : Option (Fin k), o ≠ o' → r ≤ dist (p o) (p o') := by
    intro o o' hoo'
    rcases o with _ | i <;> rcases o' with _ | i'
    · exact absurd rfl hoo'
    · simp only [p, Option.elim]
      rw [hr]; exact hf_le xs i'
    · simp only [p, Option.elim]
      rw [dist_comm, hr]; exact hf_le xs i
    · simp only [p, Option.elim]
      have hii' : i ≠ i' := fun h => hoo' (by rw [h])
      rcases lt_or_gt_of_ne hii' with h | h
      · rw [dist_comm]; exact hsep_centers i' i h
      · exact hsep_centers i i' h
  -- pigeonhole: two of these points share a cluster of `Cstar`
  let c : Option (Fin k) → Fin k := fun o =>
    (hstar.2 (p o) (Finset.mem_univ _)).exists.choose
  have hc : ∀ o, p o ∈ Cstar (c o) := fun o =>
    (hstar.2 (p o) (Finset.mem_univ _)).exists.choose_spec
  obtain ⟨o, o', hoo', hcc⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by simp)
  refine ⟨c o, ?_⟩
  have hlow : r ≤ Metric.diam (↑(Cstar (c o)) : Set X) := by
    have hmem : p o' ∈ (↑(Cstar (c o)) : Set X) := by rw [hcc]; exact hc o'
    exact (hsep o o' hoo').trans
      (Metric.dist_le_diam_of_mem (Cstar (c o)).finite_toSet.isBounded (hc o) hmem)
  linarith
