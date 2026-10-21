-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.stoneRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T02:01:21.199004+00:00
-- url     : https://prove2.me/submissions/db37eddf-fa5a-450a-9a22-ac5c73c9f1e9

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02
noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

open QAlgorithms.Papers.Independent.Renew46.P02

universe u v

theorem g65c_sep_point {B : Type u} [BooleanAlgebra B] (c : B) (hc : c ≠ ⊥) :
    ∃ z : StonePoint B, z c = true := by
  classical
  have hdis : Disjoint ((Order.PFilter.principal c : Order.PFilter B) : Set B)
      ((Order.Ideal.principal (⊥ : B)) : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : c ≤ x := Order.PFilter.mem_principal.1 hx
    have h2 : x ≤ ⊥ := Order.Ideal.mem_principal.1 hx'
    exact hc (le_bot_iff.1 (h1.trans h2))
  obtain ⟨J, hJ, -, hJF⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdis
  have hcJ : c ∉ J := by
    intro h
    exact Set.disjoint_left.1 hJF (by simp : c ∈ ((Order.PFilter.principal c : Order.PFilter B) : Set B)) h
  have hprop : Order.Ideal.IsProper J := hJ.toIsProper
  let z : StonePoint B :=
    { toFun := fun x => decide (x ∉ J)
      map_sup' := by
        intro x y
        simp only [Order.Ideal.sup_mem_iff, not_and_or]
        by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;> simp [hx, hy]
      map_inf' := by
        intro x y
        have : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
          ⟨hJ.mem_or_mem, fun h => h.elim (fun h => J.lower inf_le_left h) (fun h => J.lower inf_le_right h)⟩
        simp only [this, not_or]
        by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;> simp [hx, hy]
      map_top' := by simp [hprop.top_notMem]
      map_bot' := by simp [Order.Ideal.bot_mem] }
  exact ⟨z, by simp [z, hcJ]⟩

theorem solution (B : Type u) [BooleanAlgebra B] :
    Function.Injective (stoneSet (B := B)) ∧
    stoneSet (⊥ : B) = ∅ ∧ stoneSet (⊤ : B) = Set.univ ∧
    (∀ a b : B, stoneSet (a ⊔ b) = stoneSet a ∪ stoneSet b) ∧
    (∀ a b : B, stoneSet (a ⊓ b) = stoneSet a ∩ stoneSet b) ∧
    (∀ a : B, stoneSet aᶜ = (stoneSet a)ᶜ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    have key : ∀ x y : B, stoneSet x = stoneSet y → x \ y ≠ ⊥ → False := by
      intro x y hxy hxy'
      obtain ⟨z, hz⟩ := g65c_sep_point _ hxy'
      have h1 : z (x \ y) = (z x && !z y) := by
        rw [map_sdiff']; cases z x <;> cases z y <;> rfl
      rw [h1] at hz
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hz
      have hzx : z ∈ stoneSet x := hz.1
      rw [hxy] at hzx
      have : z y = true := hzx
      rw [hz.2] at this
      exact Bool.false_ne_true this
    rcases eq_or_ne (a \ b) ⊥ with h | h
    · rcases eq_or_ne (b \ a) ⊥ with h' | h'
      · exact hne (le_antisymm (sdiff_eq_bot_iff.1 h) (sdiff_eq_bot_iff.1 h'))
      · exact key b a hab.symm h'
    · exact key a b hab h
  · ext z; simp [stoneSet]
  · ext z; simp [stoneSet]
  · intro a b; ext z; simp [stoneSet]
  · intro a b; ext z; simp [stoneSet]
  · intro a; ext z; simp only [stoneSet, Set.mem_setOf_eq, Set.mem_compl_iff, map_compl']
    cases z a <;> simp
