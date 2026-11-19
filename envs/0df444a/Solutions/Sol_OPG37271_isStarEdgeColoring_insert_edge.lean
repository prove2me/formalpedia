-- Prove2me | solution 1 for OPG37271.isStarEdgeColoring_insert_edge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:42:09.065351+00:00
-- url     : https://prove2.me/submissions/d926a50f-0f53-447f-b43b-c13b70f4497d

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

open OPG37271

universe u

theorem solution {V : Type u} {G : SimpleGraph V} {K : Type*}
    (u v : V) (huv : G.Adj u v) (c : EdgeColoring G K)
    (hc_rest : IsStarEdgeColoring (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le {s(u, v)}) e.2⟩ :
      EdgeColoring (G.deleteEdges {s(u, v)}) K))
    (hdist : ∀ (x y : V) (hxy : G.Adj x y), s(x, y) ≠ s(u, v) →
      (x = u ∨ x = v ∨ y = u ∨ y = v ∨ G.Adj u x ∨ G.Adj v x ∨ G.Adj u y ∨ G.Adj v y) →
      c.get x y hxy ≠ c.get u v huv) :
    IsStarEdgeColoring c := by
  have hadj_rest : ∀ {a b : V}, G.Adj a b → s(a, b) ≠ s(u, v) →
      (G.deleteEdges {s(u, v)}).Adj a b := fun hab hne =>
    SimpleGraph.deleteEdges_adj.mpr ⟨hab, hne⟩
  rcases hc_rest with ⟨hprop, hpath, hcyc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b d hab had hbd
    by_cases h1 : s(a, b) = s(u, v)
    · have h2 : s(a, d) ≠ s(u, v) := by
        intro h2
        rw [Sym2.eq_iff] at h1 h2
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact hbd h2b.symm
        · exact huv.ne h2a
        · exact huv.ne h2a.symm
        · exact hbd h2b.symm
      have hdist_ad : (a = u ∨ a = v ∨ d = u ∨ d = v ∨ G.Adj u a ∨ G.Adj v a ∨ G.Adj u d ∨ G.Adj v d) := by
        rw [Sym2.eq_iff] at h1
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      have hne := hdist a d had h2 hdist_ad
      have heq : c.get a b hab = c.get u v huv :=
        congrArg (fun e : G.edgeSet => c e) (Subtype.ext h1)
      rw [heq]
      exact hne.symm
    · by_cases h2 : s(a, d) = s(u, v)
      · have hdist_ab : (a = u ∨ a = v ∨ b = u ∨ b = v ∨ G.Adj u a ∨ G.Adj v a ∨ G.Adj u b ∨ G.Adj v b) := by
          rw [Sym2.eq_iff] at h2
          rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        have hne := hdist a b hab h1 hdist_ab
        have heq : c.get a d had = c.get u v huv :=
          congrArg (fun e : G.edgeSet => c e) (Subtype.ext h2)
        rw [heq]
        exact hne
      · exact hprop a b d (hadj_rest hab h1) (hadj_rest had h2) hbd
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnodup, h₀₁, h₁₂, h₂₃, h₃₄, hc1, hc2⟩
    have hnd := hnodup
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd
    rcases hnd with ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
    by_cases e01 : s(v₀, v₁) = s(u, v)
    · have e23 : s(v₂, v₃) ≠ s(u, v) := by
        intro e23
        rw [Sym2.eq_iff] at e01 e23
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e23 with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact h02 hA.symm
        · exact h03 hB.symm
        · exact h12 hA.symm
        · exact h13 hB.symm
      have hd : v₂ = u ∨ v₂ = v ∨ v₃ = u ∨ v₃ = v ∨ G.Adj u v₂ ∨ G.Adj v v₂ ∨ G.Adj u v₃ ∨ G.Adj v v₃ := by
        rw [Sym2.eq_iff] at e01
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂))))
      have hne := hdist v₂ v₃ h₂₃ e23 hd
      have heq : c.get v₀ v₁ h₀₁ = c.get u v huv :=
        congrArg (fun e : G.edgeSet => c e) (Subtype.ext e01)
      exact hne (hc1.symm.trans heq)
    · by_cases e12 : s(v₁, v₂) = s(u, v)
      · have e34 : s(v₃, v₄) ≠ s(u, v) := by
          intro e34
          rw [Sym2.eq_iff] at e12 e34
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e34 with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exact h13 hA.symm
          · exact h14 hB.symm
          · exact h23 hA.symm
          · exact h24 hB.symm
        have hd : v₃ = u ∨ v₃ = v ∨ v₄ = u ∨ v₄ = v ∨ G.Adj u v₃ ∨ G.Adj v v₃ ∨ G.Adj u v₄ ∨ G.Adj v v₄ := by
          rw [Sym2.eq_iff] at e12
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃))))
        have hne := hdist v₃ v₄ h₃₄ e34 hd
        have heq : c.get v₁ v₂ h₁₂ = c.get u v huv :=
          congrArg (fun e : G.edgeSet => c e) (Subtype.ext e12)
        exact hne (hc2.symm.trans heq)
      · by_cases e23 : s(v₂, v₃) = s(u, v)
        · have hd : v₀ = u ∨ v₀ = v ∨ v₁ = u ∨ v₁ = v ∨ G.Adj u v₀ ∨ G.Adj v v₀ ∨ G.Adj u v₁ ∨ G.Adj v v₁ := by
            rw [Sym2.eq_iff] at e23
            rcases e23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂.symm))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁₂.symm))))))
          have hne := hdist v₀ v₁ h₀₁ e01 hd
          have heq : c.get v₂ v₃ h₂₃ = c.get u v huv :=
            congrArg (fun e : G.edgeSet => c e) (Subtype.ext e23)
          exact hne (hc1.trans heq)
        · by_cases e34 : s(v₃, v₄) = s(u, v)
          · have hd : v₁ = u ∨ v₁ = v ∨ v₂ = u ∨ v₂ = v ∨ G.Adj u v₁ ∨ G.Adj v v₁ ∨ G.Adj u v₂ ∨ G.Adj v v₂ := by
              rw [Sym2.eq_iff] at e34
              rcases e34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃.symm))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂₃.symm))))))
            have hne := hdist v₁ v₂ h₁₂ e12 hd
            have heq : c.get v₃ v₄ h₃₄ = c.get u v huv :=
              congrArg (fun e : G.edgeSet => c e) (Subtype.ext e34)
            exact hne (hc2.trans heq)
          · exact hpath ⟨v₀, v₁, v₂, v₃, v₄, hnodup,
              hadj_rest h₀₁ e01, hadj_rest h₁₂ e12, hadj_rest h₂₃ e23, hadj_rest h₃₄ e34, hc1, hc2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnodup, h₀₁, h₁₂, h₂₃, h₃₀, hc1, hc2⟩
    have hnd := hnodup
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd
    rcases hnd with ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩
    by_cases e01 : s(v₀, v₁) = s(u, v)
    · have e23 : s(v₂, v₃) ≠ s(u, v) := by
        intro e23
        rw [Sym2.eq_iff] at e01 e23
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e23 with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact h02 hA.symm
        · exact h03 hB.symm
        · exact h12 hA.symm
        · exact h13 hB.symm
      have hd : v₂ = u ∨ v₂ = v ∨ v₃ = u ∨ v₃ = v ∨ G.Adj u v₂ ∨ G.Adj v v₂ ∨ G.Adj u v₃ ∨ G.Adj v v₃ := by
        rw [Sym2.eq_iff] at e01
        rcases e01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂))))
      have hne := hdist v₂ v₃ h₂₃ e23 hd
      have heq : c.get v₀ v₁ h₀₁ = c.get u v huv :=
        congrArg (fun e : G.edgeSet => c e) (Subtype.ext e01)
      exact hne (hc1.symm.trans heq)
    · by_cases e12 : s(v₁, v₂) = s(u, v)
      · have e30 : s(v₃, v₀) ≠ s(u, v) := by
          intro e30
          rw [Sym2.eq_iff] at e12 e30
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e30 with ⟨hA, hB⟩ | ⟨hA, hB⟩
          · exact h13 hA.symm
          · exact h01 hB
          · exact h23.1 hA.symm
          · exact h02 hB
        have hd : v₃ = u ∨ v₃ = v ∨ v₀ = u ∨ v₀ = v ∨ G.Adj u v₃ ∨ G.Adj v v₃ ∨ G.Adj u v₀ ∨ G.Adj v v₀ := by
          rw [Sym2.eq_iff] at e12
          rcases e12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃))))
        have hne := hdist v₃ v₀ h₃₀ e30 hd
        have heq : c.get v₁ v₂ h₁₂ = c.get u v huv :=
          congrArg (fun e : G.edgeSet => c e) (Subtype.ext e12)
        exact hne (hc2.symm.trans heq)
      · by_cases e23 : s(v₂, v₃) = s(u, v)
        · have hd : v₀ = u ∨ v₀ = v ∨ v₁ = u ∨ v₁ = v ∨ G.Adj u v₀ ∨ G.Adj v v₀ ∨ G.Adj u v₁ ∨ G.Adj v v₁ := by
            rw [Sym2.eq_iff] at e23
            rcases e23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁₂.symm))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁₂.symm))))))
          have hne := hdist v₀ v₁ h₀₁ e01 hd
          have heq : c.get v₂ v₃ h₂₃ = c.get u v huv :=
            congrArg (fun e : G.edgeSet => c e) (Subtype.ext e23)
          exact hne (hc1.trans heq)
        · by_cases e30 : s(v₃, v₀) = s(u, v)
          · have hd : v₁ = u ∨ v₁ = v ∨ v₂ = u ∨ v₂ = v ∨ G.Adj u v₁ ∨ G.Adj v v₁ ∨ G.Adj u v₂ ∨ G.Adj v v₂ := by
              rw [Sym2.eq_iff] at e30
              rcases e30 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₂₃.symm))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂₃.symm))))))
            have hne := hdist v₁ v₂ h₁₂ e12 hd
            have heq : c.get v₃ v₀ h₃₀ = c.get u v huv :=
              congrArg (fun e : G.edgeSet => c e) (Subtype.ext e30)
            exact hne (hc2.trans heq)
          · exact hcyc ⟨v₀, v₁, v₂, v₃, hnodup,
              hadj_rest h₀₁ e01, hadj_rest h₁₂ e12, hadj_rest h₂₃ e23, hadj_rest h₃₀ e30, hc1, hc2⟩
