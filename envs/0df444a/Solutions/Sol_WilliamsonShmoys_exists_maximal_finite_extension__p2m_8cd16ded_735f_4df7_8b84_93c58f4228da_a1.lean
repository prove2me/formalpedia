-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_finite_extension__p2m_8cd16ded_735f_4df7_8b84_93c58f4228da_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:36.922045+00:00
-- url     : https://prove2.me/submissions/7e450dfc-0633-4270-b1c0-5332048d3828

import Mathlib
import Theorems.Thm_exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (H : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ P J ∧
      ∀ K : SimpleGraph V, J ≤ K → P K → K = J := by
  classical
  let s : Finset (SimpleGraph V) := Finset.univ.filter (fun J => H ≤ J ∧ P J)
  have hs : s.Nonempty := by
    refine ⟨H, ?_⟩
    simp [s, hH]
  obtain ⟨J, hJs, hmax⟩ :=
    exists_maximal_of_nonempty_finset__p2m_5ce86dee_a51b_43d9_9c16_6a53f5f31031_a3 s hs
  have hJ : H ≤ J := (Finset.mem_filter.mp hJs).2.1
  have hPJ : P J := (Finset.mem_filter.mp hJs).2.2
  refine ⟨J, hJ, hPJ, ?_⟩
  intro K hJK hPK
  have hKs : K ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ K, ?_⟩
    exact ⟨le_trans hJ hJK, hPK⟩
  exact le_antisymm (hmax K hKs hJK) hJK