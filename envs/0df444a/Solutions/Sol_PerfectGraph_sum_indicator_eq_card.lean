-- Prove2me | solution 1 for PerfectGraph.sum_indicator_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:51.520784+00:00
-- url     : https://prove2.me/submissions/7a4ddfa5-45e0-4f3c-81f1-7912b89cee72

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution {S X : Finset V} (hX : X ⊆ S) [DecidablePred (· ∈ X)] :
    ∑ u : S, (if (u : V) ∈ X then (1 : ℚ) else 0) = X.card := by
  rw [Finset.sum_coe_sort S (fun u => if u ∈ X then (1 : ℚ) else 0), Finset.sum_boole]
  congr 2
  ext u
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hX h, h⟩⟩
end PerfectGraph
