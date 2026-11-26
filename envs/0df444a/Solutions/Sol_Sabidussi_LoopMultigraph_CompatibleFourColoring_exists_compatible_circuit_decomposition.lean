-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.CompatibleFourColoring.exists_compatible_circuit_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:38.773504+00:00
-- url     : https://prove2.me/submissions/d2f019b6-5fc2-4496-8ad6-38be2f43126e

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph
import Theorems.Thm_Sabidussi_LoopMultigraph_decompose_even_edge_set
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


section
namespace Sabidussi
open scoped BigOperators
namespace LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
namespace EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)
end EulerTour
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
open Sabidussi
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
namespace CompatibleFourColoring
private theorem filter_flatMap_length {A B : Type*} (p : B → Bool)
    (f : A → List B) (xs : List A) :
    ((xs.flatMap f).filter p).length =
      (xs.map fun x ↦ ((f x).filter p).length).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]
end CompatibleFourColoring
end LoopMultigraph
end Sabidussi
end

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
open Sabidussi.LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
open Sabidussi
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
open Sabidussi.LoopMultigraph.CompatibleFourColoring
namespace Sabidussi.LoopMultigraph.CompatibleFourColoring
theorem _root_.solution
    {T : G.EulerTour} (K : G.CompatibleFourColoring T) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by
  classical
  let support : Color → Finset E := fun z ↦ Finset.univ.filter fun e ↦ K.color e = z
  have hex : ∀ z : Color, ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length =
        if e ∈ support z then 1 else 0 := by
    intro z
    exact G.decompose_even_edge_set (support z) (K.color_even z)
  choose pieces hpieces using hex
  have hpiece_subset : ∀ (z : Color) (C : G.Cycle), C ∈ pieces z → C.edges ⊆ support z := by
    intro z C hC e he
    by_contra hnot
    have hzero : ((pieces z).filter fun D ↦ e ∈ D.edges).length = 0 := by
      simpa [hnot] using hpieces z e
    have hmem : C ∈ (pieces z).filter fun D ↦ e ∈ D.edges := by
      simpa using ⟨hC, he⟩
    have hpos : 0 < ((pieces z).filter fun D ↦ e ∈ D.edges).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
    omega
  let allPieces : List G.Cycle := Finset.univ.toList.flatMap pieces
  have hcovered : ∀ e : E,
      (allPieces.filter fun C ↦ e ∈ C.edges).length = 1 := by
    intro e
    change ((Finset.univ.toList.flatMap pieces).filter fun C ↦ e ∈ C.edges).length = 1
    rw [filter_flatMap_length]
    simp_rw [hpieces]
    simp [support]
  let S : G.CircuitDecomposition :=
    { circuits := allPieces
      coveredOnce := hcovered }
  refine ⟨S, ?_⟩
  intro i C hC htransition
  change C ∈ Finset.univ.toList.flatMap pieces at hC
  rw [List.mem_flatMap] at hC
  obtain ⟨z, hz, hCz⟩ := hC
  have hprevSupport := hpiece_subset z C hCz htransition.1
  have hcurrSupport := hpiece_subset z C hCz htransition.2
  have hprevColor : K.color (T.edge (T.prev i)) = z := by
    simpa [support] using hprevSupport
  have hcurrColor : K.color (T.edge i) = z := by
    simpa [support] using hcurrSupport
  exact K.transition_ne i (hprevColor.trans hcurrColor.symm)
end Sabidussi.LoopMultigraph.CompatibleFourColoring
