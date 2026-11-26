-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.loop_sabidussi_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:20:15.462865+00:00
-- url     : https://prove2.me/submissions/2bb789cb-94b6-4022-ab56-abf01db924b8

import Definitions.Def_Sabidussi_LoopMultigraph
import Definitions.Def_Sabidussi_CyclicWord
import Definitions.Def_Sabidussi_LoopGraphBridge
import Theorems.Thm_Sabidussi_CyclicWord_Word_exists_coloring
import Theorems.Thm_Sabidussi_LoopMultigraph_CompatibleFourColoring_exists_compatible_circuit_decomposition
import Theorems.Thm_Sabidussi_LoopMultigraph_EulerTour_degree_eq_two_mul_card_occurrence


set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open Sabidussi
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LoopMultigraph V E}
namespace Sabidussi.LoopMultigraph
theorem _root_.solution (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by
  have hword : ∀ v : V, 2 ≤ Fintype.card (T.eulerWord.Occurrence v) := by
    intro v
    let e : T.eulerWord.Occurrence v ≃ T.Occurrence v := Equiv.refl _
    rw [Fintype.card_congr e]
    have hd := hmin v
    rw [T.degree_eq_two_mul_card_occurrence v] at hd
    omega
  obtain ⟨C⟩ := T.eulerWord.exists_coloring hword
  exact (T.compatibleFourColoringOfWordColoring C).exists_compatible_circuit_decomposition
end Sabidussi.LoopMultigraph
