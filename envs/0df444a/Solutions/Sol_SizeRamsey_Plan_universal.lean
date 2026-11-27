-- Prove2me | solution 1 for SizeRamsey.Plan.universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:12.511848+00:00
-- url     : https://prove2.me/submissions/9939e46c-7aed-463b-9a4e-1f4c5b15e04c

module
public import Definitions.Def_SizeRamsey_Reductions
public import Definitions.Def_SizeRamsey_Universal
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_rotate
public import Theorems.Thm_SizeRamsey_Plan_compGraph_connected
public import Theorems.Thm_SizeRamsey_Plan_compGraph_degree
public import Theorems.Thm_SizeRamsey_Plan_component_square_supported
public import Theorems.Thm_SizeRamsey_Plan_connected_positive_degree
public import Theorems.Thm_SizeRamsey_Plan_cubic_chordless_reduction
public import Theorems.Thm_SizeRamsey_Plan_degree_four_reduction
public import Theorems.Thm_SizeRamsey_Plan_degree_two_three_cases
public import Theorems.Thm_SizeRamsey_Plan_mixed_reduction
public import Theorems.Thm_SizeRamsey_Plan_square_component_reduction
public import Theorems.Thm_SizeRamsey_Plan_square_supported_degree_ge_two
public import Theorems.Thm_SizeRamsey_Plan_subcubic_chord_reduction
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_non_square_edge
public import Theorems.Thm_SizeRamsey_Plan_tau4_eq_zero_iff
public import Theorems.Thm_SizeRamsey_Plan_two_regular_square_supported
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    4 * tau4 G ≤ edgeCount G := by
  suffices h : ∀ n, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), edgeCount G = n →
      4 * tau4 G ≤ edgeCount G from h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn
  have IH : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W), edgeCount H < edgeCount G →
      4 * tau4 H ≤ edgeCount H := fun H hH => ih _ (hn ▸ hH) H rfl
  -- zero edges
  by_cases h0 : edgeCount G = 0
  · have : tau4 G = 0 := by
      rw [tau4_eq_zero_iff]
      rintro ⟨f, ⟨-, h01, -⟩⟩
      rw [edgeCount_eq_card, Finset.card_eq_zero] at h0
      have := (SimpleGraph.mem_edgeFinset (G := G) (e := s(f 0, f 1))).mpr h01
      simp_all
    omega
  -- an unsupported edge
  by_cases hsq : SquareSupported G
  swap
  · simp only [SquareSupported, not_forall] at hsq
    obtain ⟨u, v, huv, hns⟩ := hsq
    obtain ⟨ht, he⟩ := tau4_delete_non_square_edge G huv hns
    have := IH (G.deleteEdges {s(u, v)}) (by omega)
    omega
  -- a vertex of degree at least four
  by_cases h4 : ∃ v, 4 ≤ G.degree v
  · obtain ⟨v, hv⟩ := h4
    obtain ⟨ht, he⟩ := degree_four_reduction G v hv
    have := IH (erase G {v}) (by omega)
    omega
  push Not at h4
  have hdeg3 : ∀ v, G.degree v ≤ 3 := fun v => Nat.lt_succ_iff.mp (h4 v)
  -- a component containing an edge
  have hpos : 0 < edgeCount G := Nat.pos_of_ne_zero h0
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by
    rwa [← edgeCount_eq_card])
  induction e using Sym2.ind with
  | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  set C := G.connectedComponentMk a with hC
  have haC : a ∈ C.supp := rfl
  have hbC : b ∈ C.supp := (C.mem_supp_congr_adj he).mp haC
  have hCpos : 0 < edgeCount (compGraph G C) := by
    rw [edgeCount_eq_card, Finset.card_pos]
    exact ⟨s(⟨a, haC⟩, ⟨b, hbC⟩), SimpleGraph.mem_edgeFinset.mpr he⟩
  have hCcon := compGraph_connected G C
  have hCdeg : ∀ x : C.supp, (compGraph G C).degree x = 2 ∨ (compGraph G C).degree x = 3 := by
    intro x
    have hp := connected_positive_degree (compGraph G C) hCcon hCpos x
    rw [compGraph_degree] at hp ⊢
    have h2 := square_supported_degree_ge_two G hsq x.val hp
    have := hdeg3 x.val
    omega
  have hmem : ∀ f : Fin 4 → V, IsC4Map G f → f 0 ∈ C.supp → ∀ i, f i ∈ C.supp := by
    intro f hf h0 i
    obtain ⟨_, h01, h12, h23, h30⟩ := hf
    have m1 := (C.mem_supp_congr_adj h01).mp h0
    have m2 := (C.mem_supp_congr_adj h12).mp m1
    have m3 := (C.mem_supp_congr_adj h23).mp m2
    fin_cases i
    exacts [h0, m1, m2, m3]
  rcases degree_two_three_cases (compGraph G C) hCcon hCdeg with h2 | h3 | ⟨u, v, huv, hu, hv⟩
  · -- a two-regular component is a square
    have hiso := two_regular_square_supported (compGraph G C) hCcon
      (component_square_supported G hsq C) h2
    obtain ⟨ht, he⟩ := square_component_reduction G C hiso
    have := IH (erase G C.supp.toFinset) (by omega)
    omega
  · -- a cubic component: a square through the edge `ab`
    obtain ⟨f, hf, hf0, -⟩ := hsq he
    have hfC := hmem f hf (hf0 ▸ haC)
    have hfdeg : ∀ i, G.degree (f i) = 3 := fun i => by
      have := h3 ⟨f i, hfC i⟩
      rwa [compGraph_degree] at this
    by_cases hac : G.Adj (f 0) (f 2)
    · obtain ⟨ht, he, hd⟩ := subcubic_chord_reduction G hdeg3 f hf hac
      have := IH (erase G {f 0, f 1, f 2}) (by omega)
      omega
    by_cases hbd : G.Adj (f 1) (f 3)
    · have hf' := IsC4Map.rotate hf 1
      obtain ⟨ht, he, hd⟩ := subcubic_chord_reduction G hdeg3 _ hf' hbd
      have := IH (erase G {f (0 + 1), f (1 + 1), f (2 + 1)}) (by omega)
      omega
    obtain ⟨ht, he⟩ := cubic_chordless_reduction G f hfdeg hf hac hbd
    have := IH (erase G (Finset.univ.image f)) (by omega)
    omega
  · -- an adjacent pair of degrees two and three
    rw [compGraph_degree] at hu hv
    obtain ⟨ht, he⟩ := mixed_reduction G (show G.Adj u.val v.val from huv) hu hv
    have := IH (erase G {u.val, v.val}) (by omega)
    omega
end SizeRamsey.Plan
