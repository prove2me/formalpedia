-- Prove2me | solution 1 for SizeRamsey.Plan.k33_extension_tau_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:08.933638+00:00
-- url     : https://prove2.me/submissions/5e19305b-8a84-4e9e-8c8a-2c1fd64c920e

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_Extension
public import Theorems.Thm_SizeRamsey_tau4_le_card

section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
private theorem sqHit_12 : SqHit 1 2 := by unfold SqHit; decide
private theorem sqHit_45 : SqHit 4 5 := by unfold SqHit; decide
private theorem sqHit_14 : SqHit 1 4 := by unfold SqHit; decide
private theorem pathEnds_12 : PathEnds 1 2 4 5 4 5 := by unfold PathEnds; decide
private theorem pathEnds_45 : PathEnds 4 5 1 2 1 2 := by unfold PathEnds; decide
private theorem pathEnds_14 : PathEnds 1 4 0 2 3 5 := by unfold PathEnds; decide
private theorem extension_transversal
    {V : Type u} (G : SimpleGraph V) (z : V) (φ : Fin 6 → V)
    (hinj : Function.Injective φ)
    (hsurj : ∀ v, v ≠ z → ∃ i, φ i = v)
    (hadj : ∀ i j, G.Adj (φ i) (φ j) ↔ k33MinusEdge.Adj i j)
    (a b : Fin 6) (hsq : SqHit a b)
    (hpath : ∀ u x w : Fin 6, u ≠ w → G.Adj z (φ u) → G.Adj z (φ w) →
      k33MinusEdge.Adj u x → k33MinusEdge.Adj x w →
      u = a ∨ u = b ∨ x = a ∨ x = b ∨ w = a ∨ w = b) :
    c4Transversal G {φ a, φ b} := by
  intro f hf
  by_contra hno
  push Not at hno
  have hS : ∀ i, φ i ∈ ({φ a, φ b} : Finset V) → i = a ∨ i = b := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff] at hi
    exact hi
  have hnS : ∀ i, i = a ∨ i = b → φ i ∈ ({φ a, φ b} : Finset V) := by
    rintro i (rfl | rfl) <;> simp
  obtain ⟨hfi, h01, h12, h23, h30⟩ := hf
  have key : ∀ u' x' w' : V, G.Adj z u' → G.Adj u' x' → G.Adj x' w' → G.Adj w' z →
      u' ≠ w' → x' ≠ z → u' ∉ ({φ a, φ b} : Finset V) → x' ∉ ({φ a, φ b} : Finset V) →
      w' ∉ ({φ a, φ b} : Finset V) → False := by
    intro u' x' w' hzu hux hxw hwz huw hxz hu hx hw
    obtain ⟨u, rfl⟩ := hsurj u' hzu.ne.symm
    obtain ⟨x, rfl⟩ := hsurj x' hxz
    obtain ⟨w, rfl⟩ := hsurj w' hwz.ne
    rcases hpath u x w (fun h => huw (congrArg φ h)) hzu hwz.symm ((hadj _ _).1 hux)
        ((hadj _ _).1 hxw) with h | h | h | h | h | h
    · exact hu (hnS _ (Or.inl h))
    · exact hu (hnS _ (Or.inr h))
    · exact hx (hnS _ (Or.inl h))
    · exact hx (hnS _ (Or.inr h))
    · exact hw (hnS _ (Or.inl h))
    · exact hw (hnS _ (Or.inr h))
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h e => h (hfi e)
  by_cases hzf : ∃ k, f k = z
  · obtain ⟨k, hk⟩ := hzf
    fin_cases k
    · subst hk
      exact key (f 1) (f 2) (f 3) h01 h12 h23 h30 (hne 1 3 (by decide))
        (hne 2 0 (by decide)) (hno 1) (hno 2) (hno 3)
    · subst hk
      exact key (f 2) (f 3) (f 0) h12 h23 h30 h01 (hne 2 0 (by decide))
        (hne 3 1 (by decide)) (hno 2) (hno 3) (hno 0)
    · subst hk
      exact key (f 3) (f 0) (f 1) h23 h30 h01 h12 (hne 3 1 (by decide))
        (hne 0 2 (by decide)) (hno 3) (hno 0) (hno 1)
    · subst hk
      exact key (f 0) (f 1) (f 2) h30 h01 h12 h23 (hne 0 2 (by decide))
        (hne 1 3 (by decide)) (hno 0) (hno 1) (hno 2)
  · push Not at hzf
    choose g hg using fun k => hsurj (f k) (hzf k)
    have hg' : ∀ k, f k = φ (g k) := fun k => (hg k).symm
    rw [hg' 0, hg' 1] at h01
    rw [hg' 1, hg' 2] at h12
    rw [hg' 2, hg' 3] at h23
    rw [hg' 3, hg' 0] at h30
    have hgne : ∀ i j : Fin 4, i ≠ j → g i ≠ g j := fun i j h e =>
      hne i j h (by rw [hg' i, hg' j, e])
    have hmem : ∀ k, f k ∉ ({φ a, φ b} : Finset V) := hno
    rcases hsq _ _ _ _ ((hadj _ _).1 h01) ((hadj _ _).1 h12) ((hadj _ _).1 h23)
        ((hadj _ _).1 h30) (hgne 0 2 (by decide)) (hgne 1 3 (by decide)) with
      h | h | h | h | h | h | h | h
    · exact hmem 0 (hg' 0 ▸ hnS _ (Or.inl h))
    · exact hmem 0 (hg' 0 ▸ hnS _ (Or.inr h))
    · exact hmem 1 (hg' 1 ▸ hnS _ (Or.inl h))
    · exact hmem 1 (hg' 1 ▸ hnS _ (Or.inr h))
    · exact hmem 2 (hg' 2 ▸ hnS _ (Or.inl h))
    · exact hmem 2 (hg' 2 ▸ hnS _ (Or.inr h))
    · exact hmem 3 (hg' 3 ▸ hnS _ (Or.inl h))
    · exact hmem 3 (hg' 3 ▸ hnS _ (Or.inr h))
end SizeRamsey.Plan
end
end

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (z : V)
    (hiso : Nonempty (erase G {z} ≃g k33MinusEdge))
    (hdeg : G.degree z = 4) :
    tau4 G ≤ 2 := by
  obtain ⟨e⟩ := hiso
  set φ : Fin 6 → V := fun i => (e.symm i).1 with hφ
  have hinj : Function.Injective φ := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hsurj : ∀ v, v ≠ z → ∃ i, φ i = v := by
    intro v hv
    refine ⟨e ⟨v, by simpa using hv⟩, ?_⟩
    simp [hφ]
  have hadj : ∀ i j, G.Adj (φ i) (φ j) ↔ k33MinusEdge.Adj i j := fun i j =>
    e.symm.map_adj_iff
  have hcard : ∀ T : Finset (Fin 6), (∀ i ∈ T, G.Adj z (φ i)) → T.card ≤ 4 := by
    intro T hT
    have hsub : T.image φ ⊆ G.neighborFinset z := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      simpa using hT i hi
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, G.card_neighborFinset_eq_degree, hdeg] at this
    exact this
  have hpair : ∀ a b : Fin 6, c4Transversal G {φ a, φ b} → tau4 G ≤ 2 := fun a b h =>
    (tau4_le_card h).trans ((Finset.card_insert_le _ _).trans (by simp))
  by_cases h45 : G.Adj z (φ 4) ∧ G.Adj z (φ 5)
  · by_cases h12 : G.Adj z (φ 1) ∧ G.Adj z (φ 2)
    · have h0 : ¬ G.Adj z (φ 0) := by
        intro h0
        have := hcard {0, 1, 2, 4, 5} (by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl
          exacts [h0, h12.1, h12.2, h45.1, h45.2])
        exact absurd this (by decide)
      have h3 : ¬ G.Adj z (φ 3) := by
        intro h3
        have := hcard {1, 2, 3, 4, 5} (by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl
          exacts [h12.1, h12.2, h3, h45.1, h45.2])
        exact absurd this (by decide)
      refine hpair 1 4 (extension_transversal G z φ hinj hsurj hadj 1 4 sqHit_14 ?_)
      intro u x w huw hu hw hux hxw
      rcases pathEnds_14 u x w huw hux hxw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
      · exact h
      · exact absurd hu h0
      · exact absurd hw h0
      · exact absurd hu h3
      · exact absurd hw h3
    · refine hpair 4 5 (extension_transversal G z φ hinj hsurj hadj 4 5 sqHit_45 ?_)
      intro u x w huw hu hw hux hxw
      rcases pathEnds_45 u x w huw hux hxw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
      · exact h
      all_goals exact absurd ⟨by assumption, by assumption⟩ h12
  · refine hpair 1 2 (extension_transversal G z φ hinj hsurj hadj 1 2 sqHit_12 ?_)
    intro u x w huw hu hw hux hxw
    rcases pathEnds_12 u x w huw hux hxw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩
    · exact h
    all_goals exact absurd ⟨by assumption, by assumption⟩ h45
end SizeRamsey.Plan
