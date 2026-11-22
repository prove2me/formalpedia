-- Prove2me | solution 1 for Paper.Hypergraph.structure_hereditary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:01.207821+00:00
-- url     : https://prove2.me/submissions/2e61c65c-7d3c-4f25-bcaf-a32f23be4a3e

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).degeneracy ≤ H.degeneracy ∧
    (H.induce W).independenceNumber ≤ H.independenceNumber := by
  constructor
  · have hnodes : (H.induce W).incidenceVertices ⊆ H.incidenceVertices := by
      intro z hz
      cases z <;> simp_all [incidenceVertices, induce]
    have hadj : ∀ a b, (H.induce W).incidence.Adj a b → H.incidence.Adj a b := by
      intro a b
      cases a <;> cases b <;> simp [incidence, induce] <;> tauto
    have hdeg : ∀ S ⊆ H.incidenceVertices, S.Nonempty →
        ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ H.degeneracy := by
      refine csInf_mem (s := {d : ℕ | ∀ S ⊆ H.incidenceVertices, S.Nonempty →
        ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ d}) ?_
      refine ⟨H.incidenceVertices.card, ?_⟩
      intro S hS hne
      obtain ⟨v, hv⟩ := hne
      exact ⟨v, hv, (card_filter_le _ _).trans (card_le_card hS)⟩
    refine csInf_le (OrderBot.bddBelow _) ?_
    intro S hS hne
    obtain ⟨v, hv, hd⟩ := hdeg S (hS.trans hnodes) hne
    refine ⟨v, hv, le_trans ?_ hd⟩
    apply card_le_card
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1, hadj v z (mem_filter.mp hz).2⟩
  · apply Finset.sup_le
    intro S hS
    obtain ⟨hSV, hind⟩ := mem_filter.mp hS
    have hsub : S ⊆ H.vertices ∩ W := mem_powerset.mp hSV
    refine Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr
      (fun v hv => (mem_inter.mp (hsub hv)).1), ?_⟩)
    intro u hu v hv huv
    obtain ⟨hne, e, he, hue, hve⟩ := huv
    have huW := (mem_inter.mp (hsub hu)).2
    have hvW := (mem_inter.mp (hsub hv)).2
    apply hind u hu v hv
    exact ⟨hne, e, mem_filter.mpr ⟨he, ⟨u, mem_inter.mpr ⟨hue, huW⟩⟩⟩,
      mem_inter.mpr ⟨hue, huW⟩, mem_inter.mpr ⟨hve, hvW⟩⟩
end Paper.Hypergraph
