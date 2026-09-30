-- Prove2me | solution 1 for SupplyChainTheory.hakimi
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:31.650589+00:00
-- url     : https://prove2.me/submissions/a2e595dc-2ee4-4743-9e95-862b1bbbba8e

import Mathlib
import Definitions.Def_SupplyChainTheory_location

open SupplyChainTheory

theorem solution {n p : ℕ} (d : Fin n → Fin n → ℝ) (hw : Fin n → ℝ) (hwn : ∀ i, 0 ≤ hw i)
    (hp : 1 ≤ p) (hpn : p ≤ n)
    (htri : ∀ i j k : Fin n, d i k ≤ d i j + d j k)
    (X : Fin p → NetPoint n)
    (hedge : ∀ k, d (X k).u (X k).w ≤ (X k).len ∧ d (X k).w (X k).u ≤ (X k).len) :
    ∃ S : Finset (Fin n), S.card = p ∧
      ∑ i, hw i * nearestNodeDist d i S ≤ ∑ i, hw i * nearestDist d i X := by
  classical
  -- Each customer is served by a nearest point `kf i` of `X`.
  have hattain : ∀ i, ∃ k, netDist d i (X k) = nearestDist d i X := by
    intro i
    have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    obtain ⟨k, hk⟩ := (Set.range_nonempty (fun k => netDist d i (X k))).csInf_mem (Set.finite_range _)
    exact ⟨k, hk⟩
  choose kf hkf using hattain
  -- Concavity along an edge: a point is no closer than the matching mix of its endpoints.
  have hmix : ∀ i k, (1 - (X k).t) * d i (X k).u + (X k).t * d i (X k).w ≤ netDist d i (X k) := by
    intro i k
    obtain ⟨ht0, ht1⟩ := (X k).t_mem
    have h1 := htri i (X k).u (X k).w
    have h2 := htri i (X k).w (X k).u
    have e1 := (hedge k).1
    have e2 := (hedge k).2
    unfold netDist
    apply le_min <;> nlinarith
  -- Move each point of `X` to its better endpoint for the customers it serves.
  set F : Fin p → Finset (Fin n) := fun k => Finset.univ.filter (fun i => kf i = k) with hF
  set G0 : Fin p → ℝ := fun k => ∑ i ∈ F k, hw i * d i (X k).u with hG0
  set G1 : Fin p → ℝ := fun k => ∑ i ∈ F k, hw i * d i (X k).w with hG1
  set e : Fin p → Fin n := fun k => if G0 k ≤ G1 k then (X k).u else (X k).w with he
  have hmove : ∀ k, ∑ i ∈ F k, hw i * d i (e k) ≤ ∑ i ∈ F k, hw i * netDist d i (X k) := by
    intro k
    obtain ⟨ht0, ht1⟩ := (X k).t_mem
    have hlow : (1 - (X k).t) * G0 k + (X k).t * G1 k ≤ ∑ i ∈ F k, hw i * netDist d i (X k) := by
      simp only [hG0, hG1, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have := mul_le_mul_of_nonneg_left (hmix i k) (hwn i)
      nlinarith
    have hsel : ∑ i ∈ F k, hw i * d i (e k) = min (G0 k) (G1 k) := by
      by_cases hle : G0 k ≤ G1 k
      · have hek : e k = (X k).u := if_pos hle
        rw [hek, min_eq_left hle]
      · have hek : e k = (X k).w := if_neg hle
        rw [hek, min_eq_right (not_le.mp hle).le]
    rw [hsel]
    rcases le_total (G0 k) (G1 k) with hle | hle
    · rw [min_eq_left hle]; nlinarith
    · rw [min_eq_right hle]; nlinarith
  -- Pad the chosen nodes to exactly `p` nodes.
  obtain ⟨S, hSsub, -, hScard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Finset.univ.image e))
    ((Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin]))
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hpn)
  refine ⟨S, hScard, ?_⟩
  have hnode : ∀ i, nearestNodeDist d i S ≤ d i (e (kf i)) := by
    intro i
    exact csInf_le ((S.finite_toSet.image _).bddBelow)
      ⟨e (kf i), hSsub (Finset.mem_image_of_mem _ (Finset.mem_univ _)), rfl⟩
  calc ∑ i, hw i * nearestNodeDist d i S
      ≤ ∑ i, hw i * d i (e (kf i)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hnode i) (hwn i))
    _ = ∑ k, ∑ i ∈ F k, hw i * d i (e k) := by
        rw [← Finset.sum_fiberwise Finset.univ kf (fun i => hw i * d i (e (kf i)))]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i hi => ?_))
        simp only [hF, Finset.mem_filter] at hi; rw [hi.2]
    _ ≤ ∑ k, ∑ i ∈ F k, hw i * netDist d i (X k) := Finset.sum_le_sum (fun k _ => hmove k)
    _ = ∑ i, hw i * nearestDist d i X := by
        rw [← Finset.sum_fiberwise Finset.univ kf (fun i => hw i * nearestDist d i X)]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i hi => ?_))
        simp only [Finset.mem_filter] at hi; rw [← hkf i, hi.2]
