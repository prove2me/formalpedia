-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_upward_and_meet_closed
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-05T10:35:21.000233+00:00
-- url     : https://prove2.me/submissions/1e983d5c-48fd-49da-bb6d-8bf8e42bbd60

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

universe u

open Set TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P20

/-- Proposition 3.4 (de Groote, Observables I, p. 39). A quasipoint `B` is upward closed and
closed under binary meets.

Both claims follow from maximality of the filter base `B`:
* for `a ∈ B ≤ b`, add `b` to `B`: `B ∪ {b}` is again a filter base (directedness uses `a ≤ b`,
  and `b ≠ ⊥` because `a ≠ ⊥`), so maximality forces `b ∈ B`;
* for `a, b ∈ B`, add `a ⊓ b`: the meet is non-`⊥` (`B` is directed below `a` and `b`), and any
  two elements of `B ∪ {a ⊓ b}` have a common lower bound in `B` that is below both the element of
  `B` and the meet, so maximality forces `a ⊓ b ∈ B`. -/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (B : Set L)
    (hB : IsQuasipoint B) :
    (∀ a ∈ B, ∀ b : L, a ≤ b → b ∈ B) ∧
      (∀ a ∈ B, ∀ b ∈ B, a ⊓ b ∈ B) := by
  obtain ⟨hbase, hmax⟩ := hB
  obtain ⟨hne, hbot, hdir⟩ := hbase
  constructor
  · -- upward closure
    intro a ha b hab
    have hbne : b ≠ ⊥ := by
      intro h
      apply hbot
      have : a = ⊥ := le_bot_iff.1 (h ▸ hab)
      exact this ▸ ha
    have hC : IsFilterBase (B ∪ {b}) := by
      obtain ⟨y₀, hy₀⟩ := hne
      refine ⟨⟨y₀, Or.inl hy₀⟩, ?_, ?_⟩
      · simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
        exact ⟨hbot, fun h => hbne h.symm⟩
      · intro y hy z hz
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy hz ⊢
        rcases hy with hyB | rfl
        · rcases hz with hzB | rfl
          · obtain ⟨c, hcB, hcy, hcz⟩ := hdir y hyB z hzB
            exact ⟨c, Or.inl hcB, hcy, hcz⟩
          · obtain ⟨c, hcB, hcy, hca⟩ := hdir y hyB a ha
            exact ⟨c, Or.inl hcB, hcy, le_trans hca hab⟩
        · rcases hz with hzB | rfl
          · obtain ⟨c, hcB, hca, hcz⟩ := hdir a ha z hzB
            exact ⟨c, Or.inl hcB, le_trans hca hab, hcz⟩
          · obtain ⟨c, hcB, hca, _⟩ := hdir a ha a ha
            exact ⟨c, Or.inl hcB, le_trans hca hab, le_trans hca hab⟩
    have hCB : B ∪ {b} = B := hmax (B ∪ {b}) hC (Set.subset_union_left)
    have hmem : b ∈ B ∪ {b} := Set.mem_union_right _ (Set.mem_singleton b)
    rwa [hCB] at hmem
  · -- closure under meets
    intro a ha b hb
    have hmeetne : a ⊓ b ≠ ⊥ := by
      intro h
      obtain ⟨c, hcB, hca, hcb⟩ := hdir a ha b hb
      have : c = ⊥ := le_bot_iff.1 (le_trans (le_inf hca hcb) (le_of_eq h))
      exact hbot (this ▸ hcB)
    -- a common lower bound in `B` below a given `x ∈ B` and below `a ⊓ b`
    have hbelow : ∀ x ∈ B, ∃ c ∈ B, c ≤ x ∧ c ≤ a ⊓ b := by
      intro x hx
      obtain ⟨c₁, hc₁, hc₁x, hc₁a⟩ := hdir x hx a ha
      obtain ⟨c₂, hc₂, hc₂c₁, hc₂b⟩ := hdir c₁ hc₁ b hb
      exact ⟨c₂, hc₂, le_trans hc₂c₁ hc₁x, le_inf (le_trans hc₂c₁ hc₁a) hc₂b⟩
    have hC : IsFilterBase (B ∪ {a ⊓ b}) := by
      obtain ⟨y₀, hy₀⟩ := hne
      refine ⟨⟨y₀, Or.inl hy₀⟩, ?_, ?_⟩
      · simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
        exact ⟨hbot, fun h => hmeetne h.symm⟩
      · intro y hy z hz
        simp only [Set.mem_union, Set.mem_singleton_iff] at hy hz ⊢
        rcases hy with hyB | rfl
        · rcases hz with hzB | rfl
          · obtain ⟨c, hcB, hcy, hcz⟩ := hdir y hyB z hzB
            exact ⟨c, Or.inl hcB, hcy, hcz⟩
          · obtain ⟨c, hcB, hcy, hcab⟩ := hbelow y hyB
            exact ⟨c, Or.inl hcB, hcy, hcab⟩
        · rcases hz with hzB | rfl
          · obtain ⟨c, hcB, hcz, hcab⟩ := hbelow z hzB
            exact ⟨c, Or.inl hcB, hcab, hcz⟩
          · obtain ⟨c, hcB, hca, hcb⟩ := hdir a ha b hb
            exact ⟨c, Or.inl hcB, le_inf hca hcb, le_inf hca hcb⟩
    have hCB : B ∪ {a ⊓ b} = B := hmax (B ∪ {a ⊓ b}) hC (Set.subset_union_left)
    have hmem : a ⊓ b ∈ B ∪ {a ⊓ b} :=
      Set.mem_union_right _ (Set.mem_singleton (a ⊓ b))
    rwa [hCB] at hmem

end
