-- Prove2me | solution 1 for ULHC.mu_flip_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:49.786715+00:00
-- url     : https://prove2.me/submissions/59529d65-3920-421e-ab46-ee2d7465c172

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_flip_source
import Theorems.Thm_ULHC_mem_cells
import Theorems.Thm_ULHC_D_even
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F H : Finset Edge} {c : Pt} (hc : IsCell V c)
    (h : Source F c) (hD : D F H c < 0) : mu V (flip F c) H + 2 = mu V F H := by
  unfold mu
  have hcm : c ∈ cells V := mem_cells.2 hc
  rw [← Finset.add_sum_erase _ _ hcm, ← Finset.add_sum_erase _ _ hcm]
  have rest : ∑ x ∈ (cells V).erase c, (D (flip F c) H x).natAbs =
      ∑ x ∈ (cells V).erase c, (D F H x).natAbs := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [D_flip_source h x]; simp [Finset.ne_of_mem_erase hx]
  rw [rest, D_flip_source h c]; simp only [ite_true]
  obtain ⟨k, hk⟩ := D_even F H c
  rw [hk] at hD ⊢
  omega
end ULHC
