-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bounds__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:15:50.409476+00:00
-- url     : https://prove2.me/submissions/15230e00-3dbb-4ebf-91d4-631d86ffec36

import Mathlib
set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] (n e : ι → Nat)
    (hpos : ∀ i, 1 ≤ n i) (hN : 3 ≤ ∑ i, n i)
    (hsmall : ∀ i, n i ≤ 2 → e i ≤ 1)
    (hlarge : ∀ i, 3 ≤ n i → e i + 6 ≤ 3 * n i) :
    (∑ i, e i) + 6 ≤ 3 * (∑ i, n i) := by
  classical
  by_cases hnoLarge : ∀ i, n i ≤ 2
  · have hterm : ∀ i, e i ≤ n i := by
      intro i
      have he := hsmall i (hnoLarge i)
      have hn := hpos i
      omega
    have hsum : (∑ i, e i) ≤ ∑ i, n i := by
      exact Finset.sum_le_sum (fun i _hi => hterm i)
    omega
  · push_neg at hnoLarge
    obtain ⟨i, hi⟩ := hnoLarge
    have hiLarge : 3 ≤ n i := by omega
    have hbase : ∀ j, e j ≤ 3 * n j := by
      intro j
      by_cases hj : n j ≤ 2
      · have he := hsmall j hj
        have hn := hpos j
        omega
      · have hn : 3 ≤ n j := by omega
        have he := hlarge j hn
        omega
    have hterm : ∀ j, e j + (if j = i then 6 else 0) ≤ 3 * n j := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hlarge i hiLarge
      · simp [hji]
        exact hbase j
    have hsum :
        (∑ j : ι, (e j + (if j = i then 6 else 0))) ≤
          ∑ j : ι, (3 * n j) := by
      exact Finset.sum_le_sum (fun j _hj => hterm j)
    simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum