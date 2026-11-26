-- Prove2me | solution 1 for Sendov.exists_crit_multiset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:07.040545+00:00
-- url     : https://prove2.me/submissions/9fbd0df6-809d-4cf4-92fe-0396ca05703f

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Sendov_Counterexample_Factor

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n) {a : ℂ}
    (hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - a‖) :
    ∃ q : Multiset ℂ, q.card = n - 1 ∧ (∀ v ∈ q, ‖v‖ ≤ 1) ∧ (∀ v ∈ q, v ≠ 0) ∧
      derivative p = C ((n : ℂ) * p.leadingCoeff)
        * (q.map (fun v => X - C (a - v⁻¹))).prod := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdd : (derivative p).natDegree = n - 1 := by
    rw [natDegree_derivative p, hdeg]
  have hd0 : derivative p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdd
    omega
  -- Mathlib already knows the leading coefficient of a derivative
  have hlc : (derivative p).leadingCoeff = (n : ℂ) * p.leadingCoeff := by
    rw [leadingCoeff_derivative, hdeg, mul_comm]
  have hsplit : (derivative p).Splits := IsAlgClosed.splits _
  have hcard : (derivative p).roots.card = n - 1 := by
    rw [← hdd]
    exact hsplit.natDegree_eq_card_roots.symm
  have hfac := hsplit.eq_prod_roots
  -- make the root multiset opaque before rewriting anything into `hfac`
  obtain ⟨W, hW⟩ : ∃ W : Multiset ℂ, (derivative p).roots = W := ⟨_, rfl⟩
  rw [hW] at hfac hcard
  have hcrit' : ∀ w ∈ W, 1 ≤ ‖w - a‖ := by
    intro w hw
    exact hcrit w (isRoot_of_mem_roots (by rw [hW]; exact hw))
  have hne : ∀ w ∈ W, a - w ≠ 0 := by
    intro w hw h
    have h1 := hcrit' w hw
    rw [sub_eq_zero] at h
    rw [← h, sub_self, norm_zero] at h1
    linarith
  obtain ⟨q, hq⟩ : ∃ q : Multiset ℂ, q = W.map (fun w => (a - w)⁻¹) := ⟨_, rfl⟩
  have hback : q.map (fun v => a - v⁻¹) = W := by
    rw [hq, Multiset.map_map]
    have hid : ∀ w ∈ W, ((fun v => a - v⁻¹) ∘ (fun w => (a - w)⁻¹)) w = w := by
      intro w hw
      simp only [Function.comp_apply, inv_inv]
      ring
    rw [Multiset.map_congr rfl hid, Multiset.map_id']
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [hq, Multiset.card_map, hcard]
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    rw [norm_inv, inv_le_one_iff₀]
    right
    rw [norm_sub_rev]
    exact hcrit' w hw
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    exact inv_ne_zero (hne w hw)
  · rw [← hback, hlc] at hfac
    rwa [Multiset.map_map] at hfac
end Sendov
