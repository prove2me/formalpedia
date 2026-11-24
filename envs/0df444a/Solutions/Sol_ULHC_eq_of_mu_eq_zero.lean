-- Prove2me | solution 1 for ULHC.eq_of_mu_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:47.458+00:00
-- url     : https://prove2.me/submissions/9d4d2d43-41c6-42eb-a730-e2a8b47b6fb3

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_jump
import Theorems.Thm_ULHC_D_eq_zero_of_not_cell
import Theorems.Thm_ULHC_mem_cells
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
theorem _root_.solution {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : Solid V) (h0 : mu V F H = 0) :
    F = H := by
  have zero : ∀ c, D F H c = 0 := by
    intro c
    by_cases hc : IsCell V c
    · have := (Finset.sum_eq_zero_iff.1 h0) c (mem_cells.2 hc)
      simpa using this
    · exact D_eq_zero_of_not_cell hF hH hs hc
  by_contra hne
  have : (symmDiff F H).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hne (symmDiff_eq_bot.1 he)
  obtain ⟨e, he⟩ := this
  have j := D_jump hF hH e
  rw [zero, zero] at j
  rw [Finset.mem_symmDiff] at he
  unfold wD wb at j
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs at j <;> simp_all
end ULHC
