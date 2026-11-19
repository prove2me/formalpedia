-- Prove2me | solution 1 for OPG37271.isStarEdgeColoring_of_induced_matching_extension
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:21:20.113258+00:00
-- url     : https://prove2.me/submissions/bf6f4c22-8099-4d41-a754-cd276c3f0274

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

open OPG37271

universe u

theorem solution
    {V : Type u} {G M : SimpleGraph V} (hMG : M ≤ G) (c : EdgeColoring G (Fin 7))
    (hrest_star : IsStarEdgeColoring
      (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le M.edgeSet) e.2⟩ :
        EdgeColoring (G.deleteEdges M.edgeSet) (Fin 7)))
    (hrest_lt3 : ∀ x y (hxy : G.Adj x y), ¬ M.Adj x y → (c.get x y hxy).val < 3)
    (hM_ge3 : ∀ x y (hxy : M.Adj x y), 3 ≤ (c.get x y (hMG hxy)).val)
    (hM_induced : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : M.Adj x₁ y₁) (h2 : M.Adj x₂ y₂),
      s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ (hMG h1) = c.get x₂ y₂ (hMG h2) →
      x₁ ≠ x₂ ∧ x₁ ≠ y₂ ∧ y₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
        ¬ G.Adj x₁ x₂ ∧ ¬ G.Adj x₁ y₂ ∧ ¬ G.Adj y₁ x₂ ∧ ¬ G.Adj y₁ y₂) :
    IsStarEdgeColoring c := by
  have hadj_rest : ∀ {x y : V}, G.Adj x y → ¬ M.Adj x y →
      (G.deleteEdges M.edgeSet).Adj x y := fun hxy hnM =>
    SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by rwa [M.mem_edgeSet]⟩
  have hsame_M : ∀ {x₁ y₁ x₂ y₂ : V} (h1 : G.Adj x₁ y₁) (h2 : G.Adj x₂ y₂),
      c.get x₁ y₁ h1 = c.get x₂ y₂ h2 → (M.Adj x₁ y₁ ↔ M.Adj x₂ y₂) := by
    intro x₁ y₁ x₂ y₂ h1 h2 heq
    constructor
    · intro hm1
      by_contra hnm2
      have hge : 3 ≤ (c.get x₁ y₁ h1).val := hM_ge3 x₁ y₁ hm1
      have hlt : (c.get x₂ y₂ h2).val < 3 := hrest_lt3 x₂ y₂ h2 hnm2
      rw [heq] at hge
      omega
    · intro hm2
      by_contra hnm1
      have hge : 3 ≤ (c.get x₂ y₂ h2).val := hM_ge3 x₂ y₂ hm2
      have hlt : (c.get x₁ y₁ h1).val < 3 := hrest_lt3 x₁ y₁ h1 hnm1
      rw [← heq] at hge
      omega
  have hnot_M_of_mid : ∀ {x₁ y₁ x₂ y₂ : V} (h1 : G.Adj x₁ y₁) (h2 : G.Adj x₂ y₂),
      G.Adj y₁ x₂ → s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ h1 = c.get x₂ y₂ h2 → ¬ M.Adj x₁ y₁ ∧ ¬ M.Adj x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ h1 h2 hmid hne heq
    have hn1 : ¬ M.Adj x₁ y₁ := by
      intro hm1
      have hm2 : M.Adj x₂ y₂ := (hsame_M h1 h2 heq).mp hm1
      exact (hM_induced x₁ y₁ x₂ y₂ hm1 hm2 hne heq).2.2.2.2.2.2.1 hmid
    exact ⟨hn1, fun hm2 => hn1 ((hsame_M h1 h2 heq).mpr hm2)⟩
  rcases hrest_star with ⟨hprop, hpath, hcyc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v u w hvu hvw huw heq
    by_cases hm1 : M.Adj v u
    · have hm2 : M.Adj v w := (hsame_M hvu hvw heq).mp hm1
      have hne : s(v, u) ≠ s(v, w) := by
        intro hsym
        rw [Sym2.eq_iff] at hsym
        rcases hsym with ⟨_, h⟩ | ⟨h, _⟩
        · exact huw h
        · exact hvw.ne h
      exact (hM_induced v u v w hm1 hm2 hne heq).1 rfl
    · have hm2 : ¬ M.Adj v w := fun hm2 => hm1 ((hsame_M hvu hvw heq).mpr hm2)
      exact hprop v u w (hadj_rest hvu hm1) (hadj_rest hvw hm2) huw heq
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨_, n02, n03, _⟩, ⟨n12, n13, n14⟩, ⟨n23, n24⟩, _⟩
    have hne1 : s(v₀, v₁) ≠ s(v₂, v₃) := by
      intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨hA, _⟩ | ⟨hA, _⟩
      · exact n02 hA
      · exact n03 hA
    have hne2 : s(v₁, v₂) ≠ s(v₃, v₄) := by
      intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨hA, _⟩ | ⟨hA, _⟩
      · exact n13 hA
      · exact n14 hA
    obtain ⟨hm01, hm23⟩ := hnot_M_of_mid h01 h23 h12 hne1 hc1
    obtain ⟨hm12, hm34⟩ := hnot_M_of_mid h12 h34 h23 hne2 hc2
    exact hpath ⟨v₀, v₁, v₂, v₃, v₄, hnd,
      hadj_rest h01 hm01, hadj_rest h12 hm12, hadj_rest h23 hm23, hadj_rest h34 hm34, hc1, hc2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨n01, n02, n03⟩, ⟨n12, n13⟩, _⟩
    have hne1 : s(v₀, v₁) ≠ s(v₂, v₃) := by
      intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨hA, _⟩ | ⟨hA, _⟩
      · exact n02 hA
      · exact n03 hA
    have hne2 : s(v₁, v₂) ≠ s(v₃, v₀) := by
      intro h; rw [Sym2.eq_iff] at h
      rcases h with ⟨hA, _⟩ | ⟨hA, _⟩
      · exact n13 hA
      · exact n01 hA.symm
    obtain ⟨hm01, hm23⟩ := hnot_M_of_mid h01 h23 h12 hne1 hc1
    obtain ⟨hm12, hm30⟩ := hnot_M_of_mid h12 h30 h23 hne2 hc2
    exact hcyc ⟨v₀, v₁, v₂, v₃, hnd,
      hadj_rest h01 hm01, hadj_rest h12 hm12, hadj_rest h23 hm23, hadj_rest h30 hm30, hc1, hc2⟩
