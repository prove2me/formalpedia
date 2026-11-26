-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.decompose_even_edge_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:50.077176+00:00
-- url     : https://prove2.me/submissions/590e8110-5c66-4945-98d0-5ee06f1bbdbb

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph
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
private theorem even_sdiff {F D : Finset E} (hDF : D ⊆ F)
    (hF : G.IsEvenEdgeSet F) (hD : G.IsEvenEdgeSet D) :
    G.IsEvenEdgeSet (F \ D) := by
  intro v
  have hsplit := Finset.sum_sdiff hDF (f := fun e ↦ G.edgeIncidence v e)
  rw [hD v, hF v] at hsplit
  simpa using hsplit
open Sabidussi
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
namespace CompatibleFourColoring
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
namespace Sabidussi.LoopMultigraph
theorem _root_.solution (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by
  classical
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · by_cases hmin :
      (∀ D : Finset E, D.Nonempty → D ⊆ F → G.IsEvenEdgeSet D → D = F)
    · let C : G.Cycle :=
        { edges := F
          nonempty := hne
          even := hF
          minimal := hmin }
      refine ⟨[C], ?_⟩
      intro e
      by_cases he : e ∈ F <;> simp [C, he]
    · push Not at hmin
      obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
      have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
      have hRssub : F \ D ⊂ F := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨e, heD⟩ := hDne
        have : e ∈ F \ D := by simpa [heq] using hDF heD
        simp [heD] at this
      obtain ⟨LD, hLD⟩ := ih D hDssub hDeven
      obtain ⟨LR, hLR⟩ := ih (F \ D) hRssub (G.even_sdiff hDF hF hDeven)
      refine ⟨LD ++ LR, ?_⟩
      intro e
      rw [List.filter_append, List.length_append, hLD e, hLR e]
      by_cases heD : e ∈ D
      · have heF : e ∈ F := hDF heD
        simp [heD, heF]
      · by_cases heF : e ∈ F <;> simp [heD, heF]
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    exact ⟨[], by simp⟩
end Sabidussi.LoopMultigraph
