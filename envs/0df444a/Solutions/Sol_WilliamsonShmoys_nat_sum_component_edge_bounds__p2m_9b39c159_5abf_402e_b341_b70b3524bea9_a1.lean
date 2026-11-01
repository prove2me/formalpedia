-- Prove2me | solution 1 for WilliamsonShmoys.nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:03.322299+00:00
-- url     : https://prove2.me/submissions/d18884be-8169-49f6-8765-2db2e9a3399f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem solution {ι : Type} [Fintype ι] (s a : ι → ℕ)
    (hsize : 3 ≤ ∑ i : ι, s i)
    (hlocal : ∀ i,
      if 3 ≤ s i then a i ≤ 3 * s i - 6
      else if 2 ≤ s i then a i ≤ 1
      else a i = 0) :
    (∑ i : ι, a i) ≤ 3 * (∑ i : ι, s i) - 6 := by
  classical
  let cap : ℕ → ℕ := fun n =>
    if 3 ≤ n then 3 * n - 6 else if 2 ≤ n then 1 else 0
  have hcap_add (x y : ℕ) : cap x + cap y ≤ cap (x + y) := by
    unfold cap
    split_ifs <;> omega
  have hpoint (i : ι) : a i ≤ cap (s i) := by
    by_cases h3 : 3 ≤ s i
    · simpa [cap, h3] using (hlocal i)
    · by_cases h2 : 2 ≤ s i
      · have hle : a i ≤ 1 := by
          simpa [h3, h2] using (hlocal i)
        simpa [cap, h3, h2] using hle
      · have heq : a i = 0 := by
          simpa [h3, h2] using (hlocal i)
        simpa [cap, h3, h2, heq]
  have hfin (t : Finset ι) :
      t.sum (fun i => cap (s i)) ≤ cap (t.sum s) := by
    induction t using Finset.induction_on with
    | empty =>
        simp [cap]
    | @insert x t hxt ih =>
        simp only [Finset.sum_insert hxt]
        exact le_trans (Nat.add_le_add_left ih (cap (s x)))
          (hcap_add (s x) (t.sum s))
  have hsumcap :
      (∑ i : ι, cap (s i)) ≤ cap (∑ i : ι, s i) := by
    simpa using hfin Finset.univ
  calc
    (∑ i : ι, a i) ≤ ∑ i : ι, cap (s i) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ cap (∑ i : ι, s i) := hsumcap
    _ = 3 * (∑ i : ι, s i) - 6 := by
      simp [cap, hsize]