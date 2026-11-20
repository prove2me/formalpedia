-- Prove2me | solution 1 for OPG37271.isStarEdgeColoring_of_five_cycle_special_edges_and_matching
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:01:19.279597+00:00
-- url     : https://prove2.me/submissions/e6d7c43a-a04b-4616-bd20-e6a42e0add0c

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

open OPG37271
universe u

theorem solution
    {V : Type u} {G M S : SimpleGraph V} (hMG : M ≤ G) (c : EdgeColoring G (Fin 7))
    (hrest_star : IsStarEdgeColoring
      (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le M.edgeSet) e.2⟩ :
        EdgeColoring (G.deleteEdges M.edgeSet) (Fin 7)))
    (hlow : ∀ x y (hxy : G.Adj x y), ¬ M.Adj x y → ¬ S.Adj x y → (c.get x y hxy).val < 3)
    (hM_ge3 : ∀ x y (hxy : M.Adj x y), 3 ≤ (c.get x y (hMG hxy)).val)
    (hM_induced : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : M.Adj x₁ y₁) (h2 : M.Adj x₂ y₂),
      s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ (hMG h1) = c.get x₂ y₂ (hMG h2) →
      x₁ ≠ x₂ ∧ x₁ ≠ y₂ ∧ y₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
        ¬ G.Adj x₁ x₂ ∧ ¬ G.Adj x₁ y₂ ∧ ¬ G.Adj y₁ x₂ ∧ ¬ G.Adj y₁ y₂)
    (hSM_dist1 : ∀ (v u w : V) (hvu : G.Adj v u),
      S.Adj v u → (hmw : M.Adj v w) → c.get v u hvu ≠ c.get v w (hMG hmw))
    (hSM_dist2 : ∀ (x₁ y₁ x₂ y₂ : V) (h1 : G.Adj x₁ y₁),
      S.Adj x₁ y₁ → (hm : M.Adj x₂ y₂) → G.Adj y₁ x₂ →
      c.get x₁ y₁ h1 ≠ c.get x₂ y₂ (hMG hm)) :
    IsStarEdgeColoring c := by
  have hadj_rest : ∀ {x y : V}, G.Adj x y → ¬ M.Adj x y →
      (G.deleteEdges M.edgeSet).Adj x y := fun hxy hnM =>
    SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by rwa [M.mem_edgeSet]⟩
  have hS_of_ge3 : ∀ {x y : V} (hxy : G.Adj x y),
      ¬ M.Adj x y → 3 ≤ (c.get x y hxy).val → S.Adj x y := by
    intro x y hxy hnM hge3
    by_contra hnS
    have hlt3 := hlow x y hxy hnM hnS
    omega
  have hc_symm : ∀ {x y : V} (hxy : G.Adj x y), c.get x y hxy = c.get y x hxy.symm :=
    fun hxy => congrArg (fun e : G.edgeSet => c e) (Subtype.ext Sym2.eq_swap)
  -- Key lemma: any two distinct same-colored edges joined by a middle edge in G both lie outside M.
  have hnot_M_of_mid : ∀ {x₁ y₁ x₂ y₂ : V} (h1 : G.Adj x₁ y₁) (h2 : G.Adj x₂ y₂),
      G.Adj y₁ x₂ → s(x₁, y₁) ≠ s(x₂, y₂) →
      c.get x₁ y₁ h1 = c.get x₂ y₂ h2 → ¬ M.Adj x₁ y₁ ∧ ¬ M.Adj x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ h1 h2 hmid hne heq
    have hn1 : ¬ M.Adj x₁ y₁ := by
      intro hm1
      by_cases hm2 : M.Adj x₂ y₂
      · exact (hM_induced x₁ y₁ x₂ y₂ hm1 hm2 hne heq).2.2.2.2.2.2.1 hmid
      · have hge3 : 3 ≤ (c.get x₂ y₂ h2).val := heq ▸ hM_ge3 x₁ y₁ hm1
        have hs2 : S.Adj x₂ y₂ := hS_of_ge3 h2 hm2 hge3
        have hneq := hSM_dist2 y₂ x₂ y₁ x₁ h2.symm hs2.symm hm1.symm hmid.symm
        apply hneq
        rw [← hc_symm h2, ← hc_symm (hMG hm1)]
        exact heq.symm
    have hn2 : ¬ M.Adj x₂ y₂ := by
      intro hm2
      have hge3 : 3 ≤ (c.get x₁ y₁ h1).val := heq.symm ▸ hM_ge3 x₂ y₂ hm2
      have hs1 : S.Adj x₁ y₁ := hS_of_ge3 h1 hn1 hge3
      exact hSM_dist2 x₁ y₁ x₂ y₂ h1 hs1 hm2 hmid heq
    exact ⟨hn1, hn2⟩
  rcases hrest_star with ⟨hprop, hpath, hcyc⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Properness
    intro v u w hvu hvw huw heq
    by_cases hm1 : M.Adj v u
    · by_cases hm2 : M.Adj v w
      · have hne : s(v, u) ≠ s(v, w) := by
          intro hsym
          rw [Sym2.eq_iff] at hsym
          rcases hsym with ⟨_, h⟩ | ⟨h, _⟩
          · exact huw h
          · exact hvw.ne h
        exact (hM_induced v u v w hm1 hm2 hne heq).1 rfl
      · have hge3 : 3 ≤ (c.get v w hvw).val := heq ▸ hM_ge3 v u hm1
        have hs2 : S.Adj v w := hS_of_ge3 hvw hm2 hge3
        exact hSM_dist1 v w u hvw hs2 hm1 heq.symm
    · by_cases hm2 : M.Adj v w
      · have hge3 : 3 ≤ (c.get v u hvu).val := heq.symm ▸ hM_ge3 v w hm2
        have hs1 : S.Adj v u := hS_of_ge3 hvu hm1 hge3
        exact hSM_dist1 v u w hvu hs1 hm2 heq
      · exact hprop v u w (hadj_rest hvu hm1) (hadj_rest hvw hm2) huw heq
  · -- No bicolored P_4
    rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨_, n02, n03, _⟩, ⟨_, n13, n14⟩, ⟨_, _⟩, _⟩
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
  · -- No bicolored C_4
    rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨n01, n02, n03⟩, ⟨_, n13⟩, _⟩
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

