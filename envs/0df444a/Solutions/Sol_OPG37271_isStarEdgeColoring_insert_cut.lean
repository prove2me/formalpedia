-- Prove2me | solution 1 for OPG37271.isStarEdgeColoring_insert_cut
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:05:54.921196+00:00
-- url     : https://prove2.me/submissions/88f53c3c-f777-4eb4-b712-d1e212b525ad

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

open OPG37271

universe u

theorem solution {V : Type u} {G : SimpleGraph V} {K : Type*}
    (A : V → Prop) (c : EdgeColoring G K)
    (hcA : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | A v}) K))
    (hcB : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | ¬ A v}) K))
    (hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      G.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      G.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) →
      u₁ ≠ u₂ ∧ ¬ G.Adj u₁ u₂)
    (hX_B : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → (¬ A x ∨ ¬ A y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        (G.Adj u₁ x ∧ ¬ A x) ∨ G.Adj v₁ x ∨ (G.Adj u₁ y ∧ ¬ A y) ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1)
    (hX_A : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → A x → A y →
      c.get x y hxy ≠ c.get u₁ v₁ h1) :
    IsStarEdgeColoring c := by
  have hcut_dist : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        G.Adj u₁ x ∨ G.Adj v₁ x ∨ G.Adj u₁ y ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1 := by
    intro u₁ v₁ x y h1 hu₁ hv₁ hxy hne hdist
    by_cases hx : A x <;> by_cases hy : A y
    · exact hX_A u₁ v₁ x y h1 hu₁ hv₁ hxy hx hy
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inr hy) hne ?_
      have hsep := hX_sep u₁ v₁ x y h1 hu₁ hv₁ hxy hx hy hne.symm
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd rfl hsep.1
      · exact absurd hx hv₁
      · exact absurd hu₁ hy
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact absurd hux hsep.2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨huy, hy⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inl hx) hne ?_
      have hne' : s(u₁, v₁) ≠ s(y, x) := by
        intro h; apply hne; rw [Sym2.eq_swap]; exact h.symm
      have hsep := hX_sep u₁ v₁ y x h1 hu₁ hv₁ hxy.symm hy hx hne'
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd hu₁ hx
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hsep.1
      · exact absurd hy hv₁
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hux, hx⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact absurd huy hsep.2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
    · refine hX_B u₁ v₁ x y h1 hu₁ hv₁ hxy (Or.inl hx) hne ?_
      rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
      · exact absurd hu₁ hx
      · exact Or.inr (Or.inl rfl)
      · exact absurd hu₁ hy
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hux, hx⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvx)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨huy, hy⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvy))))))
  have hcut_sym : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → (A u₁ ↔ ¬ A v₁) →
      (hxy : G.Adj x y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        G.Adj u₁ x ∨ G.Adj v₁ x ∨ G.Adj u₁ y ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1 := by
    intro u₁ v₁ x y h1 hdiff hxy hne hdist
    by_cases hu₁ : A u₁
    · exact hcut_dist u₁ v₁ x y h1 hu₁ (hdiff.mp hu₁) hxy hne hdist
    · have hv₁ : A v₁ := by
        by_contra hnv₁
        exact hu₁ (hdiff.mpr hnv₁)
      have hne' : s(x, y) ≠ s(v₁, u₁) := by
        intro h; apply hne; rw [Sym2.eq_swap (a := v₁) (b := u₁)] at h; exact h
      have hdist' : x = v₁ ∨ x = u₁ ∨ y = v₁ ∨ y = u₁ ∨
          G.Adj v₁ x ∨ G.Adj u₁ x ∨ G.Adj v₁ y ∨ G.Adj u₁ y := by
        rcases hdist with h | h | h | h | h | h | h | h <;> tauto
      have hres := hcut_dist v₁ u₁ x y h1.symm hv₁ hu₁ hxy hne' hdist'
      have heq : c.get v₁ u₁ h1.symm = c.get u₁ v₁ h1 :=
        congrArg (fun e : G.edgeSet => c e) (Subtype.ext Sym2.eq_swap)
      rwa [heq] at hres
  rcases hcA with ⟨hpA, hpaA, hcyA⟩
  rcases hcB with ⟨hpB, hpaB, hcyB⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b d hab had hbd
    by_cases h1 : (A a ↔ ¬ A b)
    · exact (hcut_sym a b a d hab h1 had (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2⟩ | ⟨h1', _⟩; exact hbd h2.symm; exact hab.ne h1') (Or.inl rfl)).symm
    · by_cases h2 : (A a ↔ ¬ A d)
      · exact hcut_sym a d a b had h2 hab (by intro heq; rw [Sym2.eq_iff] at heq; rcases heq with ⟨_, h2'⟩ | ⟨h1', _⟩; exact hbd h2'; exact had.ne h1') (Or.inl rfl)
      · by_cases ha : A a
        · have hb : A b := by by_contra hnb; exact h1 ⟨fun _ => hnb, fun _ => ha⟩
          have hd : A d := by by_contra hnd; exact h2 ⟨fun _ => hnd, fun _ => ha⟩
          exact hpA ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩ hab had (fun h => hbd (congrArg Subtype.val h))
        · have hb : ¬ A b := fun hb => h1 ⟨fun h => absurd h ha, fun hn => absurd hb hn⟩
          have hd : ¬ A d := fun hd => h2 ⟨fun h => absurd h ha, fun hn => absurd hd hn⟩
          exact hpB ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩ hab had (fun h => hbd (congrArg Subtype.val h))
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨n01, n02, n03, n04⟩, ⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩
    by_cases e01 : (A v₀ ↔ ¬ A v₁)
    · have hne : s(v₂, v₃) ≠ s(v₀, v₁) := by
        intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n02 hA.symm; exact n12 hA.symm]
      exact hcut_sym v₀ v₁ v₂ v₃ h01 e01 h23 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))) hc1.symm
    · by_cases e12 : (A v₁ ↔ ¬ A v₂)
      · have hne : s(v₃, v₄) ≠ s(v₁, v₂) := by
          intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n13 hA.symm; exact n23 hA.symm]
        exact hcut_sym v₁ v₂ v₃ v₄ h12 e12 h34 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))) hc2.symm
      · by_cases e23 : (A v₂ ↔ ¬ A v₃)
        · have hne : s(v₀, v₁) ≠ s(v₂, v₃) := by
            intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n02 hA; exact n12 hB]
          exact hcut_sym v₂ v₃ v₀ v₁ h23 e23 h01 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12.symm))))))) hc1
        · by_cases e34 : (A v₃ ↔ ¬ A v₄)
          · have hne : s(v₁, v₂) ≠ s(v₃, v₄) := by
              intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n13 hA; exact n23 hB]
            exact hcut_sym v₃ v₄ v₁ v₂ h34 e34 h12 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23.symm))))))) hc2
          · by_cases h0 : A v₀
            · have h1 : A v₁ := by by_contra hn; exact e01 ⟨fun _ => hn, fun _ => h0⟩
              have h2 : A v₂ := by by_contra hn; exact e12 ⟨fun _ => hn, fun _ => h1⟩
              have h3 : A v₃ := by by_contra hn; exact e23 ⟨fun _ => hn, fun _ => h2⟩
              have h4 : A v₄ := by by_contra hn; exact e34 ⟨fun _ => hn, fun _ => h3⟩
              refine hpaA ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ⟨v₄, h4⟩, ?_, h01, h12, h23, h34, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
            · have h1 : ¬ A v₁ := fun h => e01 ⟨fun h0' => absurd h0' h0, fun hn => absurd h hn⟩
              have h2 : ¬ A v₂ := fun h => e12 ⟨fun h1' => absurd h1' h1, fun hn => absurd h hn⟩
              have h3 : ¬ A v₃ := fun h => e23 ⟨fun h2' => absurd h2' h2, fun hn => absurd h hn⟩
              have h4 : ¬ A v₄ := fun h => e34 ⟨fun h3' => absurd h3' h3, fun hn => absurd h hn⟩
              refine hpaB ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ⟨v₄, h4⟩, ?_, h01, h12, h23, h34, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨n01, n02, n03⟩, ⟨n12, n13⟩, n23⟩
    by_cases e01 : (A v₀ ↔ ¬ A v₁)
    · have hne : s(v₂, v₃) ≠ s(v₀, v₁) := by
        intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n02 hA.symm; exact n12 hA.symm]
      exact hcut_sym v₀ v₁ v₂ v₃ h01 e01 h23 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))) hc1.symm
    · by_cases e12 : (A v₁ ↔ ¬ A v₂)
      · have hne : s(v₃, v₀) ≠ s(v₁, v₂) := by
          intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨hA, _⟩ <;> [exact n13 hA.symm; exact n23.1 hA.symm]
        exact hcut_sym v₁ v₂ v₃ v₀ h12 e12 h30 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))) hc2.symm
      · by_cases e23 : (A v₂ ↔ ¬ A v₃)
        · have hne : s(v₀, v₁) ≠ s(v₂, v₃) := by
            intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n02 hA; exact n12 hB]
          exact hcut_sym v₂ v₃ v₀ v₁ h23 e23 h01 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12.symm))))))) hc1
        · by_cases e30 : (A v₃ ↔ ¬ A v₀)
          · have hne : s(v₁, v₂) ≠ s(v₃, v₀) := by
              intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨hA, _⟩ | ⟨_, hB⟩ <;> [exact n13 hA; exact n23.1 hB]
            exact hcut_sym v₃ v₀ v₁ v₂ h30 e30 h12 hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23.symm))))))) hc2
          · by_cases h0 : A v₀
            · have h1 : A v₁ := by by_contra hn; exact e01 ⟨fun _ => hn, fun _ => h0⟩
              have h2 : A v₂ := by by_contra hn; exact e12 ⟨fun _ => hn, fun _ => h1⟩
              have h3 : A v₃ := by by_contra hn; exact e23 ⟨fun _ => hn, fun _ => h2⟩
              refine hcyA ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ?_, h01, h12, h23, h30, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
            · have h1 : ¬ A v₁ := fun h => e01 ⟨fun h0' => absurd h0' h0, fun hn => absurd h hn⟩
              have h2 : ¬ A v₂ := fun h => e12 ⟨fun h1' => absurd h1' h1, fun hn => absurd h hn⟩
              have h3 : ¬ A v₃ := fun h => e23 ⟨fun h2' => absurd h2' h2, fun hn => absurd h hn⟩
              refine hcyB ⟨⟨v₀, h0⟩, ⟨v₁, h1⟩, ⟨v₂, h2⟩, ⟨v₃, h3⟩, ?_, h01, h12, h23, h30, hc1, hc2⟩
              simpa [List.nodup_cons, Subtype.ext_iff] using hnd
