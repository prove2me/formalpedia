-- Prove2me | solution 1 for Sendov.prod_norm_le_Ppolar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:36.16982+00:00
-- url     : https://prove2.me/submissions/9599b9af-22fc-4349-89bc-14787ce6ff17

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_prod_map_norm_nonneg
import Theorems.Thm_Sendov_prod_map_sq
import Theorems.Thm_Sendov_sum_norm_sq_split
import Theorems.Thm_Sendov_sum_norm_sq_le_card
import Theorems.Thm_Sendov_Multiset_prod_le_mean_pow
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
      ≤ Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hNpos : (0 : ℝ) < (q.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := t * (1 - a ^ 2) with hs
  have hcast : ∀ v : ℂ, (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v = (a : ℂ) + (s : ℂ) * v := by
    intro v
    rw [hs]
    push_cast
    ring
  simp only [hcast]
  -- the product of squares
  set P : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖)).prod with hP
  have hP0 : 0 ≤ P := prod_map_norm_nonneg q _
  have hM0 : ∀ v ∈ q, (0 : ℝ) ≤ ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 := fun v _ => sq_nonneg _
  have hamgm := Multiset.prod_le_mean_pow (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2))
    (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq] at hamgm
  set M : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum / (q.card : ℝ) with hM
  -- `M ≤ P(t)`
  have hMle : M ≤ Ppolar a x t := by
    rw [hM, div_le_iff₀ hNpos]
    have hsplit := sum_norm_sq_split a s q
    have hcard2 := sum_norm_sq_le_card q hq1
    rw [hsplit, hx, hNcast]
    have hPp : Ppolar a x t = a ^ 2 + 2 * a * s * x + s ^ 2 := by
      rw [Ppolar, hs]; ring
    rw [hPp]
    nlinarith [hcard2, hNcast, sq_nonneg s, hNpos]
  have hM0' : 0 ≤ M := by
    rw [hM]
    apply div_nonneg _ (le_of_lt hNpos)
    exact Multiset.sum_nonneg (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  -- take square roots
  have hexp : ((q.card : ℕ) : ℝ) / 2 = ((n : ℝ) - 1) / 2 := by rw [hNcast]
  have hb : (0 : ℝ) ≤ Ppolar a x t := le_trans hM0' hMle
  have hsq : (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) ^ 2 = Ppolar a x t ^ (q.card : ℕ) := by
    rw [← Real.rpow_natCast (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast (Ppolar a x t) q.card, hNcast]
    congr 1
    push_cast
    ring
  have hchain : P ^ 2 ≤ Ppolar a x t ^ (q.card : ℕ) := by
    refine hamgm.trans ?_
    exact pow_le_pow_left₀ hM0' hMle _
  rw [← hsq] at hchain
  nlinarith [hchain, hP0, Real.rpow_nonneg (le_trans hM0' hMle) (((n : ℝ) - 1) / 2)]
end Sendov
