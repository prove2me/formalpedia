-- Prove2me | solution 1 for SortingCounterexamples.Optimal.Supplement.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:16:21.246833+00:00
-- url     : https://prove2.me/submissions/4f6dba68-e435-49d2-986e-388113fa129e

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

open SortingCounterexamples.Optimal SortingCounterexamples.Optimal.Supplement

theorem SCO52_cone {n : ℕ} {D : Type*} [AddCommGroup D] [Module ℝ D] (v : Fin n → D)
    (R : Fin n → Fin n → Prop) (a b : Fin n) (hab : Relation.TransGen R a b) :
    ∃ c : Fin n × Fin n → ℝ, (∀ e, 0 ≤ c e) ∧ (∀ e, 0 < c e → R e.1 e.2) ∧
      1 ≤ ∑ e, c e ∧ v b - v a = ∑ e, c e • (v e.2 - v e.1) := by
  classical
  induction hab with
  | @single b hr =>
    refine ⟨fun e => if e = (a, b) then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro e; dsimp only; split_ifs <;> norm_num
    · intro e he
      dsimp only at he
      split_ifs at he with h1
      · subst h1; exact hr
      · norm_num at he
    · simp
    · simp [ite_smul]
  | @tail b c' _ hr ih =>
    obtain ⟨c, hc0, hcR, hc1, hcs⟩ := ih
    refine ⟨fun e => c e + if e = (b, c') then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro e; have := hc0 e; dsimp only; split_ifs <;> linarith
    · intro e he
      by_cases h1 : e = (b, c')
      · subst h1; exact hr
      · simp [h1] at he; exact hcR e he
    · rw [Finset.sum_add_distrib]; simp; linarith
    · simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hcs]; abel

theorem solution {n d : ℕ} (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n))
    (hH : IsGeometricClass v H) (h : Transcript n) :
    ∀ i : Fin n, ¬ Relation.TransGen (MajorityEdge d H h) i i := by
  classical
  intro i0 hcyc
  -- an edge exists, so the total weight is positive
  have hQpos : 0 < totalWeight H h := by
    obtain ⟨j, hj⟩ : ∃ j, MajorityEdge d H h i0 j := by
      obtain ⟨j, hj, _⟩ := Relation.TransGen.head'_iff.mp hcyc
      exact ⟨j, hj⟩
    have hQnn : 0 ≤ totalWeight H h :=
      Finset.sum_nonneg (fun π _ => by unfold weight; positivity)
    rcases hQnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h2 := hj.2
      unfold pairProb at h2
      rw [← heq, div_zero] at h2
      have : (0:ℝ) ≤ 1 - 1 / ((d : ℝ) + 1) := by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith
      linarith
  obtain ⟨c, hc0, hcR, hc1, hcs⟩ := SCO52_cone v (MajorityEdge d H h) i0 i0 hcyc
  rw [sub_self] at hcs
  set u : Fin n × Fin n → (Fin d → ℝ) := fun e => v e.2 - v e.1 with hu
  set t := Finset.univ.filter (fun e : Fin n × Fin n => 0 < c e) with ht
  have hsum_t : ∑ e ∈ t, c e = ∑ e, c e := by
    rw [ht, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with hce
    · rfl
    · exact (le_antisymm (not_lt.mp hce) (hc0 e)).symm
  have hsmul_t : ∑ e ∈ t, c e • u e = ∑ e, c e • u e := by
    rw [ht, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with hce
    · rfl
    · rw [le_antisymm (not_lt.mp hce) (hc0 e), zero_smul]
  have hmem : (0 : Fin d → ℝ) ∈ convexHull ℝ (u '' {e | MajorityEdge d H h e.1 e.2}) := by
    have := Finset.centerMass_mem_convexHull (R := ℝ) (s := u '' {e | MajorityEdge d H h e.1 e.2})
      t (w := c) (fun e _ => hc0 e) (by rw [hsum_t]; linarith) (z := u)
      (fun e he => ⟨e, hcR e (Finset.mem_filter.mp he).2, rfl⟩)
    rwa [Finset.centerMass, hsmul_t, ← hcs, smul_zero] at this
  obtain ⟨ι, _, z, μ, hzs, hai, hμ0, hμ1, hμz⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hcard : Fintype.card ι ≤ d + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    rw [Module.finrank_fin_fun] at h2
    omega
  -- choose edges
  have hz : ∀ k, ∃ e : Fin n × Fin n, MajorityEdge d H h e.1 e.2 ∧ u e = z k := by
    intro k
    obtain ⟨e, he, hez⟩ := hzs ⟨k, rfl⟩
    exact ⟨e, he, hez⟩
  choose E hE hEz using hz
  -- every ranking in H violates some chosen edge
  have hviol : ∀ π ∈ H, ∃ k, ¬ π.Before (E k).1 (E k).2 := by
    intro π hπ
    obtain ⟨w, hw⟩ := hH π hπ
    by_contra hall
    push Not at hall
    have hpos : ∀ k, 0 < ∑ l, z k l * w l := by
      intro k
      have := (hw _ _).mp (hall k)
      rw [← hEz k, hu]
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      unfold score at this
      linarith
    have hzero : ∑ k, μ k * ∑ l, z k l * w l = 0 := by
      have : ∀ l, ∑ k, μ k * z k l = 0 := by
        intro l
        have := congrFun hμz l
        simpa [Finset.sum_apply] using this
      calc ∑ k, μ k * ∑ l, z k l * w l = ∑ l, (∑ k, μ k * z k l) * w l := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
        _ = 0 := by simp [this]
    have hne : (Finset.univ : Finset ι).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      rw [hem, Finset.sum_empty] at hμ1; norm_num at hμ1
    have : 0 < ∑ k, μ k * ∑ l, z k l * w l :=
      Finset.sum_pos (fun k _ => mul_pos (hμ0 k) (hpos k)) hne
    linarith
  -- weight of rankings violating an edge
  have hbad : ∀ k, ∑ π ∈ H.filter (fun π => ¬ π.Before (E k).1 (E k).2), weight h π
      < totalWeight H h / ((d : ℝ) + 1) := by
    intro k
    have hp := (hE k).2
    unfold pairProb at hp
    have hsplit := Finset.sum_filter_add_sum_filter_not H (fun π => π.Before (E k).1 (E k).2)
      (fun π => weight h π)
    have hd1 : (0:ℝ) < (d : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hQpos] at hp
    unfold totalWeight at hp ⊢
    have : (1 - 1 / ((d:ℝ) + 1)) * (∑ π ∈ H, weight h π)
        = (∑ π ∈ H, weight h π) - (∑ π ∈ H, weight h π) / ((d:ℝ) + 1) := by ring
    linarith
  have hcover : totalWeight H h ≤ ∑ k, ∑ π ∈ H.filter (fun π => ¬ π.Before (E k).1 (E k).2),
      weight h π := by
    unfold totalWeight
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro π hπ
    obtain ⟨k, hk⟩ := hviol π hπ
    have hw : 0 ≤ weight h π := by unfold weight; positivity
    calc weight h π = (if ¬ π.Before (E k).1 (E k).2 then weight h π else 0) := by simp [hk]
      _ ≤ ∑ k', (if ¬ π.Before (E k').1 (E k').2 then weight h π else 0) :=
        Finset.single_le_sum (f := fun k' => if ¬ π.Before (E k').1 (E k').2 then weight h π else 0)
          (fun k' _ => by split_ifs <;> linarith) (Finset.mem_univ k)
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    rw [hem, Finset.sum_empty] at hμ1; norm_num at hμ1
  have hlt : ∑ k, ∑ π ∈ H.filter (fun π => ¬ π.Before (E k).1 (E k).2), weight h π
      < ∑ _k : ι, totalWeight H h / ((d : ℝ) + 1) :=
    Finset.sum_lt_sum_of_nonempty hne (fun k _ => hbad k)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hlt
  have hc : (Fintype.card ι : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hcard
  have : (Fintype.card ι : ℝ) * (totalWeight H h / ((d : ℝ) + 1)) ≤ totalWeight H h := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith
