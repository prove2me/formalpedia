-- Prove2me | solution 1 for WilliamsonShmoys.bakerRoot_eq_of_min
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T16:03:00.884227+00:00
-- url     : https://prove2.me/submissions/201f0edc-85d6-45c1-927b-674cd6843918

import Mathlib
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (r v : Fin n) (hrv : G.Reachable r v)
    (hmin : ∀ u, u < r → ¬ G.Reachable u r) :
    WilliamsonShmoys.bakerRoot G v = r := by
  unfold WilliamsonShmoys.bakerRoot
  apply le_antisymm
  · apply Finset.min'_le
    simpa using hrv
  · apply Finset.le_min'
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    by_contra hlt
    exact hmin u (lt_of_not_ge hlt) (hu.trans hrv.symm)
