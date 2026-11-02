-- Prove2me | solution 1 for WilliamsonShmoys.cut_implies_not_reachable__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:27.650204+00:00
-- url     : https://prove2.me/submissions/a06da2df-e2e9-4455-a3f1-2c478100e3b8

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (A : Set V)
    (huA : u ∈ A) (hvA : v ∉ A)
    (hcut : ∀ {x y : V}, x ∈ A → y ∉ A → ¬ G.Adj x y) :
    ¬ G.Reachable u v := by
  intro hreach
  rw [G.reachable_iff_reflTransGen] at hreach
  have hstay : ∀ {x : V}, Relation.ReflTransGen G.Adj u x → x ∈ A := by
    intro x hpath
    induction hpath with
    | refl => exact huA
    | tail hpath hyz ih =>
        by_contra hz
        exact hcut ih hz hyz
  exact hvA (hstay hreach)