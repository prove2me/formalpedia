-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bound_arithmetic__p2m_1501895e_8d06_4c19_968a_5139d07078f6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:22:53.104916+00:00
-- url     : https://prove2.me/submissions/068a99ad-64b9-440e-ae2a-a8169142a009

import Mathlib
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1

set_option autoImplicit false

theorem solution
    {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (htotal : 3 ≤ ∑ i ∈ parts, c i)
    (hlarge : ∀ i ∈ parts, 3 ≤ c i → e i + 6 ≤ 3 * c i)
    (hsmall : ∀ i ∈ parts, c i < 3 → e i ≤ c i - 1) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by
  have hpoint : ∀ i ∈ parts, e i ≤ 3 * c i := by
    intro i hi
    by_cases hc : 3 ≤ c i
    · have h := hlarge i hi hc
      omega
    · have hs := hsmall i hi (by omega)
      omega
  by_cases hex : ∃ i ∈ parts, e i + 6 ≤ 3 * c i
  · exact WilliamsonShmoys.sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1 parts c e hpoint hex
  · have hallsmall : ∀ i ∈ parts, c i < 3 := by
      intro i hi
      by_contra hc
      apply hex
      exact ⟨i, hi, hlarge i hi (by omega)⟩
    have hunit : ∀ i ∈ parts, e i ≤ c i := by
      intro i hi
      have hs := hsmall i hi (hallsmall i hi)
      omega
    exact WilliamsonShmoys.sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1 parts c e htotal hunit