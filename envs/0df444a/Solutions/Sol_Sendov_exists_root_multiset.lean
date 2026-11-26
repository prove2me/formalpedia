-- Prove2me | solution 1 for Sendov.exists_root_multiset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:59.546307+00:00
-- url     : https://prove2.me/submissions/f0f1ac32-20dd-4aa9-94c4-abd5e68a1027

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Sendov_Counterexample_Factor

set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ z : Multiset ℂ, z.card = n - 1 ∧ (∀ w ∈ z, ‖w‖ ≤ 1) ∧
      p = C p.leadingCoeff * ((X - C a) * (z.map (fun w => X - C w)).prod) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact hsplit.natDegree_eq_card_roots.symm
  have hmem : a ∈ p.roots := by
    rw [mem_roots hp0]
    exact hpa
  obtain ⟨z, hz⟩ : ∃ z : Multiset ℂ, p.roots = a ::ₘ z :=
    ⟨p.roots.erase a, (Multiset.cons_erase hmem).symm⟩
  have hfac := hsplit.eq_prod_roots
  rw [hz] at hfac hcard
  refine ⟨z, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons] at hcard
    omega
  · intro w hw
    exact hroots w (by rw [hz]; exact Multiset.mem_cons_of_mem hw)
  · rwa [Multiset.map_cons, Multiset.prod_cons] at hfac
end Sendov
