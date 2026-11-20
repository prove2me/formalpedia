-- Prove2me | solution 1 for WeightedRainbowCycle.Weighted.density_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:46:58.138174+00:00
-- url     : https://prove2.me/submissions/82a37a0f-9cb5-4702-a1ff-62c4b1071123

import Mathlib
import Definitions.Def_WeightedRainbowCycle_Weighted_Subgraph

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Dev.DensityExpansion

open WeightedRainbowCycle.Weighted

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C]

omit [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq C] in
lemma edges_empty (G : Model V E C) (K : Subgraph G) (hK : K.verts.card < 2) :
    K.edges = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  have hmem : e ∈ G.graph.edgeSet := by rw [G.allEdges]; trivial
  obtain ⟨u, v, huv⟩ := Graph.exists_isLink_of_mem_edgeSet hmem
  have hne : u ≠ v := by
    rintro rfl
    exact G.loopless e u huv
  have hu := K.incident_mem e he u ⟨v, huv⟩
  have hv := K.incident_mem e he v ⟨u, huv.symm⟩
  have : 2 ≤ K.verts.card := by
    have := Finset.card_le_card (show ({u, v} : Finset V) ⊆ K.verts by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    rwa [Finset.card_pair hne] at this
  omega

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma degree_nonneg (G : Model V E C) (H : Subgraph G) : 0 ≤ H.degree := by
  unfold Subgraph.degree
  exact div_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun e _ => G.weight_nonneg e)) (Nat.cast_nonneg _)

lemma sub_bound (G : Model V E C) (H : Subgraph G) (hmax : H.IsDensityMax)
    (K : Subgraph G) :
    ∑ e ∈ K.edges, G.weight e ≤
      H.degree * K.verts.card * Real.log K.verts.card / (2 * Real.log H.verts.card) := by
  have hn : (2 : ℝ) ≤ H.verts.card := by exact_mod_cast hmax.1
  have hlogn : 0 < Real.log H.verts.card := Real.log_pos (by linarith)
  have hd := degree_nonneg G H
  by_cases hK : 2 ≤ K.verts.card
  · have h := hmax.2 K hK
    have hk : (2 : ℝ) ≤ K.verts.card := by exact_mod_cast hK
    have hlogk : 0 < Real.log K.verts.card := Real.log_pos (by linarith)
    rw [div_le_div_iff₀ hlogk hlogn] at h
    have hdeg : K.degree * K.verts.card = 2 * ∑ e ∈ K.edges, G.weight e := by
      unfold Subgraph.degree
      field_simp
    rw [le_div_iff₀ (by positivity)]
    have : K.degree * K.verts.card * Real.log H.verts.card ≤
        H.degree * Real.log K.verts.card * K.verts.card := by nlinarith
    nlinarith
  · rw [edges_empty G K (by omega)]
    simp only [Finset.sum_empty]
    have : 0 ≤ Real.log K.verts.card := Real.log_natCast_nonneg _
    positivity

end WeightedRainbowCycle.Dev.DensityExpansion

namespace WeightedRainbowCycle.Weighted

theorem chk_density_expansion {V E C : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    (G : Model V E C) (H : Subgraph G) (hmax : H.IsDensityMax)
    (S : Finset V) (hS : S.Nonempty) (hSH : S ⊆ H.verts) :
    H.degree / (2 * Real.log H.verts.card) * Real.log ((H.verts.card : ℝ) / S.card) ≤
      H.boundaryMass S / S.card := by
  classical
  open WeightedRainbowCycle.Dev.DensityExpansion in
  have hn : (2 : ℝ) ≤ H.verts.card := by exact_mod_cast hmax.1
  have hlogn : 0 < Real.log H.verts.card := Real.log_pos (by linarith)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hsn : (S.card : ℝ) ≤ H.verts.card := by exact_mod_cast Finset.card_le_card hSH
  have hd := WeightedRainbowCycle.Dev.DensityExpansion.degree_nonneg G H
  set n : ℝ := (H.verts.card : ℝ) with hn_def
  set s : ℝ := (S.card : ℝ) with hs_def
  let K1 : Subgraph G := ⟨S, H.edges.filter (fun e => ∀ u, G.graph.Inc e u → u ∈ S),
    fun e he u hu => (Finset.mem_filter.1 he).2 u hu⟩
  let K2 : Subgraph G := ⟨H.verts \ S,
    H.edges.filter (fun e => ∀ u, G.graph.Inc e u → u ∈ H.verts \ S),
    fun e he u hu => (Finset.mem_filter.1 he).2 u hu⟩
  have b1 := WeightedRainbowCycle.Dev.DensityExpansion.sub_bound G H hmax K1
  have b2 := WeightedRainbowCycle.Dev.DensityExpansion.sub_bound G H hmax K2
  have hK2card : (K2.verts.card : ℝ) = n - s := by
    show (((H.verts \ S).card : ℕ) : ℝ) = _
    rw [Finset.card_sdiff_of_subset hSH]
    push_cast [Nat.cast_sub (Finset.card_le_card hSH)]
    rfl
  have hK1card : (K1.verts.card : ℝ) = s := rfl
  rw [hK1card] at b1
  rw [hK2card] at b2
  -- edge partition
  have key : ∀ e ∈ H.edges, G.weight e ≤
      (if (∀ u, G.graph.Inc e u → u ∈ S) then G.weight e else 0) +
      (if (∀ u, G.graph.Inc e u → u ∈ H.verts \ S) then G.weight e else 0) +
      (if ∃ u ∈ S, ∃ v, v ∉ S ∧ G.graph.IsLink e u v then G.weight e else 0) := by
    intro e he
    have w0 := G.weight_nonneg e
    by_cases h1 : ∀ u, G.graph.Inc e u → u ∈ S
    · rw [if_pos h1]
      split_ifs <;> linarith
    by_cases h2 : ∀ u, G.graph.Inc e u → u ∈ H.verts \ S
    · rw [if_pos h2]
      split_ifs <;> linarith
    have hbd : ∃ u ∈ S, ∃ v, v ∉ S ∧ G.graph.IsLink e u v := by
      push Not at h1 h2
      obtain ⟨a, ha, haS⟩ := h1
      obtain ⟨b, hb, hbS⟩ := h2
      have hbH : b ∈ H.verts := H.incident_mem e he b hb
      have hbS' : b ∈ S := by
        by_contra hh
        exact hbS (Finset.mem_sdiff.2 ⟨hbH, hh⟩)
      obtain ⟨c, hbc⟩ := hb
      obtain ⟨d', had⟩ := ha
      refine ⟨b, hbS', c, ?_, hbc⟩
      rcases hbc.eq_and_eq_or_eq_and_eq had with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd (h ▸ hbS') haS
      · rw [h]; exact haS
    simp only [h1, h2, hbd, if_true, if_false]
    linarith
  have hsum : ∑ e ∈ H.edges, G.weight e ≤
      ∑ e ∈ K1.edges, G.weight e + ∑ e ∈ K2.edges, G.weight e + H.boundaryMass S := by
    refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [K1, K2, Finset.sum_filter, Subgraph.boundaryMass]
  have hn0 : n ≠ 0 := by linarith
  have hW : ∑ e ∈ H.edges, G.weight e = H.degree * n / 2 := by
    unfold Subgraph.degree
    rw [← hn_def]
    field_simp
  have hn0 : n ≠ 0 := by linarith
  -- final
  have hlog : Real.log (n / s) = Real.log n - Real.log s :=
    Real.log_div hn0 hs.ne'
  have hlogK2 : Real.log (n - s) ≤ Real.log n := by
    by_cases h : n - s = 0
    · rw [h, Real.log_zero]; exact hlogn.le
    · exact Real.log_le_log (by rcases (sub_nonneg.2 hsn).lt_or_eq with h' | h'
                                · exact h'
                                · exact absurd h'.symm h) (by linarith)
  have hb2' : ∑ e ∈ K2.edges, G.weight e ≤ H.degree * (n - s) / 2 := by
    refine b2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ H.degree * (n - s) := mul_nonneg hd (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogK2 this]
  have hb1' : (∑ e ∈ K1.edges, G.weight e) * (2 * Real.log n) ≤
      H.degree * s * Real.log s := by
    rw [le_div_iff₀ (by positivity)] at b1
    exact b1
  rw [hlog, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hs]
  have hB : H.boundaryMass S ≥ ∑ e ∈ H.edges, G.weight e - ∑ e ∈ K1.edges, G.weight e
      - ∑ e ∈ K2.edges, G.weight e := by linarith
  set B := H.boundaryMass S
  set w1 := ∑ e ∈ K1.edges, G.weight e
  rw [hW] at hB
  -- goal: d*(log n - log s) * s ≤ B * (2 log n)
  have : H.degree * n / 2 - w1 - H.degree * (n - s) / 2 ≤ B := by linarith
  have h3 : (H.degree * n / 2 - w1 - H.degree * (n - s) / 2) * (2 * Real.log n) ≤
      B * (2 * Real.log n) := mul_le_mul_of_nonneg_right this (by positivity)
  nlinarith

end WeightedRainbowCycle.Weighted
end

theorem solution : type_of% @WeightedRainbowCycle.Weighted.chk_density_expansion := @WeightedRainbowCycle.Weighted.chk_density_expansion
