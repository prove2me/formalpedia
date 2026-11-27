-- Prove2me | solution 1 for SizeRamsey.Proof.connected_transversal_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:05.911342+00:00
-- url     : https://prove2.me/submissions/ae176c4a-d16f-43b1-8977-3968f693d302

module
public import Definitions.Def_SizeRamsey_Equality
public import Definitions.Def_SizeRamsey_ColoringBase
public import Definitions.Def_SizeRamsey_Coloring
public import Theorems.Thm_SizeRamsey_Plan_edgeCount_iso
public import Theorems.Thm_SizeRamsey_Plan_small_graph_data
public import Theorems.Thm_SizeRamsey_Proof_equality_classification
public import Theorems.Thm_SizeRamsey_Proof_four_mul_tau4_le_edgeCount
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof
namespace SizeRamsey.Proof
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hle : edgeCount G ≤ 16) :
    ∃ S : Finset V,
      c4Transversal G S ∧ S.card ≤ 3 := by
  obtain ⟨S, hS, hcard⟩ := exists_transversal_card_eq_tau4 G
  refine ⟨S, hS, ?_⟩
  rw [hcard]
  by_contra hnot
  have hu := Proof.four_mul_tau4_le_edgeCount G
  have hm : edgeCount G = 16 := by omega
  have heq : 4 * tau4 G = edgeCount G := by omega
  have hclass := (Proof.equality_classification G hconn (by omega) hle).mp heq
  obtain ⟨hC, hW, hK, hO⟩ := Plan.small_graph_data
  rcases hclass with hC4 | hW5 | hK33 | hOct
  · obtain ⟨e⟩ := hC4
    have hi := Plan.edgeCount_iso e
    omega
  · obtain ⟨e⟩ := hW5
    have hi := Plan.edgeCount_iso e
    omega
  · obtain ⟨e⟩ := hK33
    have hi := Plan.edgeCount_iso e
    omega
  · obtain ⟨e⟩ := hOct
    have hi := Plan.edgeCount_iso e
    omega
end SizeRamsey.Proof
