-- Prove2me | solution 1 for QuarterSumLadder.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:53:54.969599+00:00
-- url     : https://prove2.me/submissions/fae7712d-c59b-48a6-b195-2d59e3e3949a

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨g, ?_, fun u => ?_⟩
  · rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  · exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg u))
end QuarterSumLadder
