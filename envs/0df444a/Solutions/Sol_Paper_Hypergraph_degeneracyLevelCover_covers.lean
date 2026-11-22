-- Prove2me | solution 1 for Paper.Hypergraph.degeneracyLevelCover_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:21.95581+00:00
-- url     : https://prove2.me/submissions/e58ad4d1-6e0d-4d28-92f9-1307e28eaa5f

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_incidence_order_right_card
import Theorems.Thm_Paper_Hypergraph_degeneracyLevelCover_nonneg
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_nonneg


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ} {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : H.Cover x y)
    (hinj : Set.InjOn rank (↑H.incidenceVertices : Set (ℕ ⊕ ℕ)))
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    (hq : ∀ e ∈ H.edges, ∀ v ∈ H.edge e, d v - x v ≤ q e ∧ q e ≤ d v) (r : ℝ) :
    H.Cover (indicator (H.levelSeparator x d r)) (fun e => H.degeneracyLevelCover rank x d y q e r) := by
  let m := fun e => H.degeneracyLevelCover rank x d y q e r
  have hm : ∀ e ∈ H.edges, 0 ≤ m e := fun e he => H.degeneracyLevelCover_nonneg rank hx hy.1 he r
  refine ⟨hm, ?_⟩
  intro v hv
  let I := H.edges.filter (fun e => v ∈ H.edge e)
  by_cases hvS : v ∈ H.levelSeparator x d r
  swap
  · simp only [indicator, if_neg hvS]
    exact sum_nonneg (fun e he => hm e (mem_filter.mp he).1)
  have hvsel := (mem_filter.mp hvS).2
  have hxv : 0 < x v := lt_of_le_of_ne (hx v hv) hvsel.1.symm
  have hvm : vertexMultiplier x d v r = 1 / x v :=
    Set.indicator_of_mem (show r ∈ Set.Icc (d v - x v) (d v) from hvsel.2) _
  let L := I.filter (fun e => rank (.inr e) < rank (.inl v))
  let U := I.filter (fun e => ¬rank (.inr e) < rank (.inl v))
  have hLI : L ⊆ I := filter_subset _ _
  have hUI : U ⊆ I := filter_subset _ _
  have hI : I ⊆ H.edges := filter_subset _ _
  have hsum : (∑ e ∈ L, y e) + (∑ e ∈ U, y e) = ∑ e ∈ I, y e := sum_filter_add_sum_filter_not _ _ _
  simp only [indicator, if_pos hvS]
  change 1 ≤ ∑ e ∈ I, m e
  by_cases hleft : x v / 2 ≤ ∑ e ∈ L, y e
  · have hscale : 1 ≤ (2 / x v) * ∑ e ∈ L, y e := by
      have hh := mul_le_mul_of_nonneg_left hleft (by positivity : 0 ≤ 2 / x v)
      have heq : (2 / x v) * (x v / 2) = 1 := by field_simp
      rwa [heq] at hh
    calc
      1 ≤ (2 / x v) * ∑ e ∈ L, y e := hscale
      _ = ∑ e ∈ L, (2 / x v) * y e := mul_sum _ _ _
      _ ≤ ∑ e ∈ L, m e := by
        apply sum_le_sum
        intro e he
        have heE := hI (hLI he)
        have hye := hy.1 e heE
        have hve := (mem_filter.mp (hLI he)).2
        have hrank := (mem_filter.mp he).2
        have hs : 2 * y e * vertexMultiplier x d v r ≤
            ∑ w ∈ (H.edge e).filter (fun w => rank (.inr e) < rank (.inl w)), 2 * y e * vertexMultiplier x d w r := by
          apply single_le_sum (f := fun w => 2 * y e * vertexMultiplier x d w r) (a := v)
          · intro w hw
            exact mul_nonneg (by positivity)
              (vertexMultiplier_nonneg (hx w (H.edge_subset e heE (mem_filter.mp hw).1)) r)
          · exact mem_filter.mpr ⟨hve, hrank⟩
        have hright : 0 ≤ (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator
            (fun _ => (1 : ℝ)) r := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        change _ ≤ _ + _
        rw [hvm] at hs
        have heq : (2 / x v) * y e = 2 * y e * (1 / x v) := by ring
        rw [heq]
        linarith
      _ ≤ ∑ e ∈ I, m e := sum_le_sum_of_subset_of_nonneg hLI (fun e he _ => hm e (hI he))
  · have hright : x v / 2 < ∑ e ∈ U, y e := by
      have h := hy.2 v hv
      change x v ≤ ∑ e ∈ I, y e at h
      linarith
    have hU : U.Nonempty := by
      by_contra h
      have h0 := Finset.not_nonempty_iff_eq_empty.mp h
      rw [h0, sum_empty] at hright
      linarith
    obtain ⟨e, heU, hemax⟩ := U.exists_max_image y hU
    have heE := hI (hUI heU)
    have hye := hy.1 e heE
    have hUsub : U ⊆ H.edges.filter (fun f => v ∈ H.edge f ∧ rank (.inl v) < rank (.inr f)) := by
      intro f hf
      obtain ⟨hfI, hnot⟩ := mem_filter.mp hf
      obtain ⟨hfE, hvf⟩ := mem_filter.mp hfI
      have hvI : Sum.inl v ∈ H.incidenceVertices := by simp [incidenceVertices, hv]
      have hfI' : Sum.inr f ∈ H.incidenceVertices := by simp [incidenceVertices, hfE]
      have hne : rank (.inl v) ≠ rank (.inr f) := by
        intro h
        have hh := hinj hvI hfI' h
        cases hh
      exact mem_filter.mpr ⟨hfE, hvf, by omega⟩
    have hcard : (U.card : ℝ) ≤ H.degeneracy := by
      exact_mod_cast (card_le_card hUsub).trans (H.incidence_order_right_card hlater hv)
    have hys : (∑ f ∈ U, y f) ≤ (U.card : ℝ) * y e := by
      calc
        _ ≤ ∑ _f ∈ U, y e := sum_le_sum hemax
        _ = _ := by simp
    have hsmall : x v ≤ 2 * H.degeneracy * y e := by
      have hh := mul_le_mul_of_nonneg_right hcard hye
      nlinarith
    have hve := (mem_filter.mp (hUI heU)).2
    have hqv := hq e heE v hve
    have hrwin : r ∈ Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e) :=
      ⟨by linarith [hvsel.2.1, hvsel.2.2], by linarith [hvsel.2.1, hvsel.2.2]⟩
    have hme : 1 ≤ m e := by
      dsimp [m, degeneracyLevelCover]
      rw [Set.indicator_of_mem hrwin]
      have hn : 0 ≤ ∑ w ∈ (H.edge e).filter (fun w => rank (.inr e) < rank (.inl w)),
          2 * y e * vertexMultiplier x d w r := sum_nonneg (fun w hw =>
        mul_nonneg (by positivity) (vertexMultiplier_nonneg (hx w (H.edge_subset e heE (mem_filter.mp hw).1)) r))
      linarith
    exact hme.trans (single_le_sum (fun f hf => hm f (hI hf)) (hUI heU))
end Paper.Hypergraph
