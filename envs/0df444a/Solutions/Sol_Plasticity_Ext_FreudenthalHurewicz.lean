-- Prove2me | solution 1 for Plasticity.Ext.FreudenthalHurewicz
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:15:33.021984+00:00
-- url     : https://prove2.me/submissions/163d7e40-e61e-4472-9f6b-f39e243a02bb

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Sequences

/-!
Freudenthal–Hurewicz (1936): a nonexpansive map of a compact metric space onto itself
preserves distances.

Proof: for `x, y ∈ K` take backward orbits `a 0 = x`, `f (a (n+1)) = a n` and likewise `b`
for `y`. Distances `dist (a n) (b n)` increase with `n`. By compactness of `K × K` there are
`k < m` with `a k, a m` and `b k, b m` close; pushing forward `k + 1` times shows that
`f x` is close to `a (m - k - 1)` and `f y` close to `b (m - k - 1)`, so
`dist x y ≤ dist (a (m-k-1)) (b (m-k-1)) ≤ dist (f x) (f y) + ε`.
-/

open Filter Topology

namespace Sol_Plasticity_Ext_FreudenthalHurewicz

/-- A backward orbit of `x` under a map `f` of `K` onto `K`. -/
lemma backward_orbit {M : Type*} (K : Set M) (f : M → M) (hsurj : Set.SurjOn f K K)
    (x : M) (hx : x ∈ K) :
    ∃ a : ℕ → M, a 0 = x ∧ (∀ n, a n ∈ K) ∧ ∀ n, f (a (n + 1)) = a n := by
  have hpre : ∀ z ∈ K, ∃ w, w ∈ K ∧ f w = z := fun z hz => hsurj hz
  choose! g hgK hfg using hpre
  have hK : ∀ n, g^[n] x ∈ K := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hgK _ ih
  refine ⟨fun n => g^[n] x, rfl, hK, fun n => ?_⟩
  show f (g^[n + 1] x) = g^[n] x
  rw [Function.iterate_succ_apply']
  exact hfg _ (hK n)

/-- Along two backward orbits, distances can only grow when both indices are shifted. -/
lemma shift_le {M : Type*} [MetricSpace M] (K : Set M) (f : M → M)
    (hd : ∀ u ∈ K, ∀ v ∈ K, dist (f u) (f v) ≤ dist u v)
    (a b : ℕ → M) (haK : ∀ n, a n ∈ K) (hbK : ∀ n, b n ∈ K)
    (ha : ∀ n, f (a (n + 1)) = a n) (hb : ∀ n, f (b (n + 1)) = b n) (i j k : ℕ) :
    dist (a i) (b j) ≤ dist (a (i + k)) (b (j + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc dist (a i) (b j) ≤ dist (a (i + k)) (b (j + k)) := ih
      _ = dist (f (a (i + k + 1))) (f (b (j + k + 1))) := by rw [ha, hb]
      _ ≤ dist (a (i + k + 1)) (b (j + k + 1)) := hd _ (haK _) _ (hbK _)
      _ = dist (a (i + (k + 1))) (b (j + (k + 1))) := by rw [← add_assoc, ← add_assoc]

end Sol_Plasticity_Ext_FreudenthalHurewicz

open Sol_Plasticity_Ext_FreudenthalHurewicz in
theorem solution {M : Type*} [MetricSpace M] (K : Set M) (hK : IsCompact K)
    (f : M → M) (hmaps : Set.MapsTo f K K) (hsurj : Set.SurjOn f K K)
    (hlip : LipschitzOnWith 1 f K) :
    ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) = dist x y := by
  have hd : ∀ u ∈ K, ∀ v ∈ K, dist (f u) (f v) ≤ dist u v := by
    intro u hu v hv
    simpa using hlip.dist_le_mul u hu v hv
  intro x hx y hy
  refine le_antisymm (hd x hx y hy) ?_
  obtain ⟨a, ha0, haK, ha⟩ := backward_orbit K f hsurj x hx
  obtain ⟨b, hb0, hbK, hb⟩ := backward_orbit K f hsurj y hy
  -- the key estimate, given a pair of indices `k < m` where both orbits nearly recur
  have key : ∀ ε > 0, ∀ k m, k < m → dist (a k) (a m) < ε / 2 → dist (b k) (b m) < ε / 2 →
      dist x y < dist (f x) (f y) + ε := by
    intro ε hε k m hkm h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, m = k + (j + 1) := ⟨m - (k + 1), by omega⟩
    have ea : dist (a 0) (a (j + 1)) ≤ dist (a k) (a (k + (j + 1))) := by
      have := shift_le K f hd a a haK haK ha ha 0 (j + 1) k
      rwa [zero_add, add_comm (j + 1) k] at this
    have eb : dist (b 0) (b (j + 1)) ≤ dist (b k) (b (k + (j + 1))) := by
      have := shift_le K f hd b b hbK hbK hb hb 0 (j + 1) k
      rwa [zero_add, add_comm (j + 1) k] at this
    have fa : dist (f x) (a j) < ε / 2 := by
      rw [← ha0, ← ha j]
      exact lt_of_le_of_lt (hd _ (haK 0) _ (haK _)) (lt_of_le_of_lt ea h1)
    have fb : dist (f y) (b j) < ε / 2 := by
      rw [← hb0, ← hb j]
      exact lt_of_le_of_lt (hd _ (hbK 0) _ (hbK _)) (lt_of_le_of_lt eb h2)
    have mono : dist x y ≤ dist (a j) (b j) := by
      have := shift_le K f hd a b haK hbK ha hb 0 0 j
      rwa [zero_add, ha0, hb0] at this
    calc dist x y ≤ dist (a j) (b j) := mono
      _ ≤ dist (a j) (f x) + dist (f x) (f y) + dist (f y) (b j) := dist_triangle4 _ _ _ _
      _ < ε / 2 + dist (f x) (f y) + ε / 2 := by
          rw [dist_comm (a j)]
          linarith
      _ = dist (f x) (f y) + ε := by ring
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨p, -, φ, hφ, hlim⟩ :=
    (hK.prod hK).tendsto_subseq (x := fun n => (a n, b n)) (fun n => ⟨haK n, hbK n⟩)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε / 4) (by positivity)
  have h1 : dist (a (φ N), b (φ N)) p < ε / 4 := hN N le_rfl
  have h2 : dist (a (φ (N + 1)), b (φ (N + 1))) p < ε / 4 := hN (N + 1) (Nat.le_succ N)
  have hpair : dist (a (φ N), b (φ N)) (a (φ (N + 1)), b (φ (N + 1))) < ε / 2 := by
    calc _ ≤ dist (a (φ N), b (φ N)) p + dist p (a (φ (N + 1)), b (φ (N + 1))) :=
          dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by rw [dist_comm p]; exact add_lt_add h1 h2
      _ = ε / 2 := by ring
  rw [Prod.dist_eq] at hpair
  exact key ε hε (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
    (lt_of_le_of_lt (le_max_left _ _) hpair) (lt_of_le_of_lt (le_max_right _ _) hpair)
