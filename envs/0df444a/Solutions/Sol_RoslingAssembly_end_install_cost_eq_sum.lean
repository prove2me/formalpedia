-- Prove2me | solution 1 for RoslingAssembly.end_install_cost_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:08:22.524978+00:00
-- url     : https://prove2.me/submissions/f2034214-38f2-4d69-99cd-6de08b6ee8b2

import Mathlib
import Definitions.Def_RoslingAssembly_Network_h
open RoslingAssembly

theorem solution{N : ℕ} [NeZero N] (net : Network N) (H : Fin N → ℝ) :
    H 0 = ∑ i, net.h H i := by
  simp only [Network.h, Network.P, Finset.sum_sub_distrib, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin N, (∑ i, if net.s k = some i then H k else 0) =
      if k = 0 then 0 else H k := by
    intro k
    rcases hs : net.s k with _ | j
    · have h0 := (net.s_eq_none_iff k).mp hs
      have : k = 0 := Fin.ext (by simp [h0])
      simp [this]
    · have : k ≠ 0 := by
        rintro rfl
        rw [(net.s_eq_none_iff 0).mpr (by simp)] at hs
        cases hs
      simp [this]
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  have he := Finset.add_sum_erase Finset.univ H (Finset.mem_univ (0 : Fin N))
  have h2 : (∑ k, if k = (0 : Fin N) then (0 : ℝ) else H k) = ∑ k ∈ Finset.univ.erase 0, H k := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne']
  rw [h2]
  linarith
