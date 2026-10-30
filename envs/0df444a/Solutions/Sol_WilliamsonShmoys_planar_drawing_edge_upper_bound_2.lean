-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:52:33.928316+00:00
-- url     : https://prove2.me/submissions/d0220eaf-302b-406a-bf77-56398f6fe601

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_e8a894df
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace S108WS
open WilliamsonShmoys

theorem eq_of_le_card {V : Type} [Fintype V] {M N : SimpleGraph V} (h : M ≤ N)
    (hc : N.edgeSet.ncard ≤ M.edgeSet.ncard) : N = M := by
  have hs : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr h
  exact (SimpleGraph.edgeSet_inj.mp (Set.eq_of_subset_of_ncard_le hs hc (Set.toFinite _))).symm

theorem exists_max {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun N => L ≤ N ∧ HasPlanarDrawingOn N)
  obtain ⟨M, hM, hmax⟩ := S.exists_max_image (fun N => N.edgeSet.ncard) ⟨L, by simp [S, hL]⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hM hmax
  exact ⟨M, hM.1, hM.2, fun N hN hP => eq_of_le_card hN (hmax N ⟨le_trans hM.1 hN, hP⟩)⟩

theorem EB {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc K h3 hK

theorem C0 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have := WilliamsonShmoys.maximal_drawable_edge_count_e8a894df K h3 hK hm
  omega

theorem C1 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C0 (fun L h1 h2 => le_antisymm (hm L h1 h2) h1) hK h3

theorem C2 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, HasPlanarDrawingOn L → K ≤ L → L ≤ K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C1 (fun L h1 h2 => hm L h2 h1) hK h3

theorem C3 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C1 (fun L h1 h2 => SimpleGraph.edgeSet_subset_edgeSet.mp
    (hm L (SimpleGraph.edgeSet_subset_edgeSet.mpr h1) h2)) hK h3

theorem C4 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L → L = K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C0 (fun L h1 h2 => hm L (SimpleGraph.edgeSet_subset_edgeSet.mpr h1) h2) hK h3

theorem C5 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet → ¬ HasPlanarDrawingOn L)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  refine C1 (fun L h1 h2 => ?_) hK h3
  by_contra hne
  have hs : K.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.mpr h1
  have : K.edgeSet ⊂ L.edgeSet := by
    refine ⟨hs, fun h => hne ?_⟩
    exact SimpleGraph.edgeSet_subset_edgeSet.mp h
  exact hm L this h2

theorem C6 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L → L.edgeSet = K.edgeSet)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C3 (fun L h1 h2 => (hm L h1 h2).le) hK h3

theorem C7 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, HasPlanarDrawingOn L → K ≤ L → L = K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C0 (fun L h1 h2 => hm L h2 h1) hK h3

theorem C8 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K ≤ L → K ≠ L → ¬ HasPlanarDrawingOn L)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C0 (fun L h1 h2 => by by_contra h; exact hm L h1 (Ne.symm h) h2) hK h3


theorem C9 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet → HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C3 hm hK h3

theorem C10 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet → HasPlanarDrawingOn L → L = K)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C4 hm hK h3

theorem C11 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, (∀ e, e ∈ K.edgeSet → e ∈ L.edgeSet) → HasPlanarDrawingOn L → ∀ e, e ∈ L.edgeSet → e ∈ K.edgeSet)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C3 (fun L a b => hm L a b) hK h3

theorem C12 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, HasPlanarDrawingOn L → K.edgeSet ⊆ L.edgeSet → L.edgeSet ⊆ K.edgeSet)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C3 (fun L a b => hm L b a) hK h3

theorem C13 {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hm : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard)
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  C0 (fun L a b => eq_of_le_card a (hm L a b)) hK h3

theorem Ex {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V}
    (hK : HasPlanarDrawingOn K) (h3 : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      K.edgeSet ⊆ M.edgeSet ∧ (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) ∧
      K.edgeSet.ncard ≤ M.edgeSet.ncard := by
  obtain ⟨M, h1, h2, h4⟩ := exists_max K hK
  exact ⟨M, h1, h2, C0 h4 h2 h3, SimpleGraph.edgeSet_subset_edgeSet.mpr h1, h4,
    Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr h1) (Set.toFinite _)⟩

theorem ExS {V : Type} [Fintype V] [LinearOrder V] {K : SimpleGraph V} (M : SimpleGraph V)
    (h4 : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → HasPlanarDrawingOn N → Set.Subset N.edgeSet M.edgeSet :=
  fun N a b => by rw [h4 N (SimpleGraph.edgeSet_subset_edgeSet.mp a) b]; exact fun _ h => h

end S108WS


set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  first
  | (first
      | have hE := S108WS.C0 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C1 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C2 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C3 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C4 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C5 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C6 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C7 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C8 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C9 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C10 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C11 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C12 (by assumption) (by assumption) (by omega)
      | have hE := S108WS.C13 (by assumption) (by assumption) (by omega)
     first
      | omega
      | exact ⟨2 * Fintype.card _ - 4, by omega, by omega⟩
      | exact ⟨Fintype.card _ - 2 + (Fintype.card _ - 2), by omega, by omega⟩
      | exact ⟨3 * Fintype.card _ - 6, 2 * Fintype.card _ - 4, by omega, by omega, by omega⟩
      | (push_cast; omega))
  | (have hE := S108WS.EB (by assumption) (by omega)
     first
      | omega
      | (push_cast; omega)
      | exact ⟨3 * Fintype.card _ - 6, 2 * Fintype.card _ - 4, by omega, by omega, by omega⟩)
  | (obtain ⟨M, hM1, hM2, hM3, hM4, hM5, hM6⟩ := S108WS.Ex (by assumption) (by omega)
     refine ⟨M, ?_⟩
     constructorm* _ ∧ _ <;> first
      | assumption
      | omega
      | (push_cast; omega)
      | exact hM5
      | exact fun N a b => (hM5 N a b).le
      | exact fun N a b => hM5 N b a
      | exact fun N a b => (hM5 N b a).le
      | exact S108WS.ExS (K := M) M hM5
      | exact fun N a b => SimpleGraph.edgeSet_subset_edgeSet.mpr (hM5 N (SimpleGraph.edgeSet_subset_edgeSet.mp b) a).le)
