-- Prove2me | solution 1 for SizeRamsey.Plan.classified_three_degree_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:59.229465+00:00
-- url     : https://prove2.me/submissions/21e905b8-1baf-4d6b-8637-2c0a84756113

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_k33_three_degree_two_absurd
public import Theorems.Thm_SizeRamsey_Plan_small_degrees

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Classified G) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.degree a = 2)
    (hb : G.degree b = 2)
    (hc : G.degree c = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by
  obtain ⟨-, d2, d3, d4⟩ := small_degrees
  rcases h with h | h | h | h
  · exact h
  all_goals obtain ⟨e⟩ := h
  · exfalso
    have := d2 (e a)
    rw [e.degree_eq, ha] at this
    split_ifs at this <;> omega
  · exfalso
    have key : ∀ x, G.degree x = 2 → e x = 0 ∨ e x = 3 := by
      intro x hx
      have := d3 (e x)
      rw [e.degree_eq, hx] at this
      split_ifs at this with h'
      · exact h'
      · omega
    exact k33_three_degree_two_absurd (e a) (e b) (e c) (e.injective.ne hab)
      (e.injective.ne hac) (e.injective.ne hbc) (key a ha) (key b hb) (key c hc)
  · exfalso
    have := d4 (e a)
    rw [e.degree_eq, ha] at this
    omega
end SizeRamsey.Plan
