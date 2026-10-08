-- Prove2me | solution 1 for TheoryOfGames.Decomposition.decomposable_iff_splitting
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:09:35.464985+00:00
-- url     : https://prove2.me/submissions/3e7f9e81-12b4-4486-a968-ba7a17a5611e

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem f2a66268_cs_constituent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (P : Finset ι)
    (hP : ∀ S : Finset ι, S ⊆ P → v S + v (P \ S) = v P) :
    IsConstantSum (constituent v P) where
  empty := by simp [constituent, hv.empty]
  compl := by
    intro S
    simp only [constituent]
    have h1 : (Sᶜ).map (Function.Embedding.subtype (· ∈ P))
        = P \ S.map (Function.Embedding.subtype (· ∈ P)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
        refine Finset.mem_sdiff.2 ⟨a.2, ?_⟩
        intro h
        obtain ⟨b, hb, hba⟩ := Finset.mem_map.1 h
        have : b = a := Subtype.ext hba
        subst this
        exact (Finset.mem_compl.1 ha) hb
      · intro hx
        obtain ⟨hxP, hxS⟩ := Finset.mem_sdiff.1 hx
        refine Finset.mem_map.2 ⟨⟨x, hxP⟩, ?_, rfl⟩
        refine Finset.mem_compl.2 ?_
        intro h
        exact hxS (Finset.mem_map.2 ⟨⟨x, hxP⟩, h, rfl⟩)
    have h2 : (Finset.univ : Finset P).map (Function.Embedding.subtype (· ∈ P)) = P := by
      ext x
      constructor
      · intro hx
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact a.2
      · intro hx
        exact Finset.mem_map.2 ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
    rw [h1, h2]
    apply hP
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
    exact a.2
  superadd := by
    intro S T hST
    simp only [constituent]
    rw [Finset.map_union]
    exact hv.superadd _ _ (Finset.disjoint_map _ |>.2 hST)

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) :
    (IsDecomposable v J ↔ IsSplitting v J) ∧
      (IsSplitting v J ↔ ∀ R : Finset ι, v R = v (R ∩ J) + v (R ∩ Jᶜ)) := by
  have h23 : IsSplitting v J ↔ ∀ R : Finset ι, v R = v (R ∩ J) + v (R ∩ Jᶜ) := by
    constructor
    · intro h R
      have := h (R ∩ J) (R ∩ Jᶜ) Finset.inter_subset_right Finset.inter_subset_right
      rw [← this]
      congr 1
      ext x
      by_cases hx : x ∈ J <;> simp [hx]
    · intro h S T hS hT
      rw [h (S ∪ T)]
      have e1 : (S ∪ T) ∩ J = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.1 (Finset.mem_inter.1 hx).1 with h' | h'
          · exact h'
          · exact absurd (Finset.mem_inter.1 hx).2 (Finset.mem_compl.1 (hT h'))
        · intro hx
          exact Finset.mem_inter.2 ⟨Finset.mem_union_left _ hx, hS hx⟩
      have e2 : (S ∪ T) ∩ Jᶜ = T := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.1 (Finset.mem_inter.1 hx).1 with h' | h'
          · exact absurd (hS h') (Finset.mem_compl.1 (Finset.mem_inter.1 hx).2)
          · exact h'
        · intro hx
          exact Finset.mem_inter.2 ⟨Finset.mem_union_right _ hx, hT hx⟩
      rw [e1, e2]
  refine ⟨⟨?_, ?_⟩, h23⟩
  · rintro ⟨vΔ, vH, hΔ, hH, h⟩ S T hS hT
    rw [h, h S, h T]
    have a1 : (S ∪ T).subtype (· ∈ J) = S.subtype (· ∈ J) := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_subtype, Finset.mem_union]
      constructor
      · rintro (h' | h')
        · exact h'
        · exact absurd hx (Finset.mem_compl.1 (hT h'))
      · intro h'; exact Or.inl h'
    have a2 : (S ∪ T).subtype (· ∈ Jᶜ) = T.subtype (· ∈ Jᶜ) := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_subtype, Finset.mem_union]
      constructor
      · rintro (h' | h')
        · exact absurd (hS h') (Finset.mem_compl.1 hx)
        · exact h'
      · intro h'; exact Or.inr h'
    have a3 : T.subtype (· ∈ J) = ∅ := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_subtype, Finset.notMem_empty, iff_false]
      intro h'
      exact (Finset.mem_compl.1 (hT h')) hx
    have a4 : S.subtype (· ∈ Jᶜ) = ∅ := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_subtype, Finset.notMem_empty, iff_false]
      intro h'
      exact (Finset.mem_compl.1 hx) (hS h')
    rw [a1, a2, a3, a4, hΔ.empty, hH.empty]
    ring
  · intro hs
    have h3 := h23.1 hs
    refine ⟨constituent v J, constituent v Jᶜ,
      f2a66268_cs_constituent v hv J ?_, f2a66268_cs_constituent v hv Jᶜ ?_, ?_⟩
    · intro S hS
      have k1 := h3 Sᶜ
      have k2 := hv.compl S
      have k3 := hv.compl J
      have e1 : Sᶜ ∩ J = J \ S := by
        ext x; simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]; tauto
      have e2 : Sᶜ ∩ Jᶜ = Jᶜ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_compl]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨fun h' => h (hS h'), h⟩
      rw [e1, e2] at k1
      linarith
    · intro T hT
      have k1 := h3 Tᶜ
      have k2 := hv.compl T
      have k3 := hv.compl J
      have e1 : Tᶜ ∩ J = J := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_compl]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨fun h' => (Finset.mem_compl.1 (hT h')) h, h⟩
      have e2 : Tᶜ ∩ Jᶜ = Jᶜ \ T := by
        ext x; simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]; tauto
      rw [e1, e2] at k1
      linarith
    · intro R
      simp only [constituent, Finset.subtype_map]
      rw [h3 R]
      congr 2
      all_goals (ext x; simp)
