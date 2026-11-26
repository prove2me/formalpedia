-- Prove2me | solution 1 for Sendov.defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:21.265799+00:00
-- url     : https://prove2.me/submissions/f0e86c6f-606c-420e-a7c4-ec9d248d2476

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect
import Theorems.Thm_Sendov_prod_norm_nonneg
import Theorems.Thm_Sendov_prod_norm_le_one
import Theorems.Thm_Sendov_norm_mul_norm_inv_sub_conj_le

set_option autoImplicit false
open Sendov
open Multiset
namespace Sendov
theorem _root_.solution : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod * (s.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - ((s.map (fun z => ‖z‖)).prod) ^ 2 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    have hP1 : (t.map (fun z => ‖z‖)).prod ≤ 1 := prod_norm_le_one t ht
    have hT0 : 0 ≤ (t.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum := by
      refine Multiset.sum_nonneg ?_
      intro y hy
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
      exact norm_nonneg _
    have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpt := norm_mul_norm_inv_sub_conj_le hw
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    -- `r P (δ + T) = P (r δ) + r (P T) ≤ P(1-r²) + r(1-P²) ≤ 1 - r²P²`
    have hstep1 := mul_le_mul_of_nonneg_left hpt hP0
    have hstep2 := mul_le_mul_of_nonneg_left hIH hr0
    have hfac : 0 ≤ (1 - ‖w‖) * (1 - (t.map (fun z => ‖z‖)).prod)
        * (1 - ‖w‖ * (t.map (fun z => ‖z‖)).prod) := by
      have h3 : ‖w‖ * (t.map (fun z => ‖z‖)).prod ≤ 1 := by nlinarith
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [hstep1, hstep2, hfac]
end Sendov
