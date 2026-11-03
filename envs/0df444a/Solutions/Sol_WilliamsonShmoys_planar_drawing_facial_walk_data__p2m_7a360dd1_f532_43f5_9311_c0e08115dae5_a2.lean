-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:17:51.331965+00:00
-- url     : https://prove2.me/submissions/4062e950-d5f3-4434-8aa0-1fb97f3f591f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

private theorem partition_into_long_lists {α : Type} (k : ℕ) (l : List α)
    (hk : 0 < k) (hl : 3 * k ≤ l.length) :
    ∃ ls : List (List α), ls.length = k ∧ ls.flatten = l ∧
      ∀ x ∈ ls, 3 ≤ x.length := by
  induction k generalizing l with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨[l], by simp, by simp, ?_⟩
      simpa using hl
    | succ n =>
      have hlen : 3 ≤ l.length := by omega
      have hdrop : 3 * (n + 1) ≤ (l.drop 3).length := by
        simp only [List.length_drop]
        omega
      obtain ⟨ls, hls, hflat, hlong⟩ := ih (l.drop 3) (by omega) hdrop
      refine ⟨l.take 3 :: ls, by simp [hls], ?_, ?_⟩
      · simp only [List.flatten_cons, hflat, List.take_append_drop]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [List.length_take, Nat.min_eq_left hlen]
        · exact hlong x hx

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (k : ℕ) (faces : Fin k → List (V × V)),
      (∀ i, 3 ≤ (faces i).length) ∧
      (letI : DecidableRel G.Adj := dG; ∀ u v,
        (List.flatten (List.ofFn faces)).count (u, v) =
          if G.Adj u v then 1 else 0) ∧
      Fintype.card V + k =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨F, inst, len, heuler, hmin, hsum⟩ :=
    face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5 G hG hConn hcard
  letI : Fintype F := inst
  have he : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at heuler hsum
  have hk : 0 < Fintype.card F := by
    by_contra hn
    have hz : Fintype.card F = 0 := Nat.eq_zero_of_not_pos hn
    letI : IsEmpty F := Fintype.card_eq_zero_iff.mp hz
    have hzero : (∑ f : F, len f) = 0 := by simp
    rw [hzero] at hsum
    omega
  have hbound : 3 * Fintype.card F ≤ 2 * G.edgeFinset.card := by
    calc
      3 * Fintype.card F = ∑ _f : F, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ f : F, len f := Finset.sum_le_sum (fun f _ => hmin f)
      _ = 2 * G.edgeFinset.card := hsum
  let edges : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  let l : List (V × V) := edges.toList
  have hlen : l.length = 2 * G.edgeFinset.card := by
    simp only [l, Finset.length_toList, edges]
    exact G.two_mul_card_edgeFinset.symm
  obtain ⟨ls, hls, hflat, hlong⟩ :=
    partition_into_long_lists (Fintype.card F) l hk (by omega)
  let faces : Fin ls.length → List (V × V) := ls.get
  refine ⟨ls.length, faces, ?_, ?_, ?_⟩
  · intro i
    exact hlong (faces i) (List.get_mem ls i)
  · intro u v
    have hflatten : (List.ofFn faces).flatten = l := by
      simpa [faces, List.ofFn_get] using hflat
    rw [hflatten]
    simp only [l, List.Nodup.count (Finset.nodup_toList edges), Finset.mem_toList,
      edges, Finset.mem_filter, Finset.mem_univ, true_and]
  · simpa [hls] using heuler
