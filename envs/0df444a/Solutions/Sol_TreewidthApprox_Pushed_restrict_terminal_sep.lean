-- Prove2me | solution 1 for TreewidthApprox.Pushed.restrict_terminal_sep
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:13:07.508483+00:00
-- url     : https://prove2.me/submissions/147efa25-53b4-4f8c-ac36-85a1eec3cda0

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false
open TreewidthApprox.Pushed

theorem p3_iff {V : Type} [DecidableEq V] {W P Q R : Finset V} :
    IsPartition3 W P Q R ↔ ∀ v, ((v ∈ P ∨ v ∈ Q ∨ v ∈ R) ↔ v ∈ W) ∧ ¬ (v ∈ P ∧ v ∈ Q) ∧
      ¬ (v ∈ P ∧ v ∈ R) ∧ ¬ (v ∈ Q ∧ v ∈ R) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ v
    refine ⟨?_, fun h => Finset.disjoint_left.mp h1 h.1 h.2,
      fun h => Finset.disjoint_left.mp h2 h.1 h.2, fun h => Finset.disjoint_left.mp h3 h.1 h.2⟩
    rw [← h4]; simp only [Finset.mem_union]; tauto
  · intro h
    refine ⟨Finset.disjoint_left.mpr fun v hv hv' => (h v).2.1 ⟨hv, hv'⟩,
      Finset.disjoint_left.mpr fun v hv hv' => (h v).2.2.1 ⟨hv, hv'⟩,
      Finset.disjoint_left.mpr fun v hv hv' => (h v).2.2.2 ⟨hv, hv'⟩, ?_⟩
    ext v; simp only [Finset.mem_union]; rw [or_assoc]; exact (h v).1

theorem restr_side {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    IsTerminalSep G (A ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A).card
        (L ∩ (A ∪ B)) (X ∩ A) (R ∩ (A ∪ B)) := by
  refine ⟨?_, ?_, ?_, ?_, le_refl _⟩
  · rw [p3_iff]
    intro v
    have hL := (p3_iff.mp hLXR.1) v
    have hd : v ∈ A → v ∉ B := fun h => Finset.disjoint_left.mp hAB h
    simp only [Finset.mem_univ, iff_true] at hL
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  · intro v hv
    simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
    tauto
  · intro v hv
    simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
    tauto
  · intro a ha b hb
    simp only [Finset.mem_inter] at ha hb
    exact hLXR.2 a ha.1 b hb.1

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    IsTerminalSep G (A₁ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₁).card
        (L ∩ (A₁ ∪ B)) (X ∩ A₁) (R ∩ (A₁ ∪ B)) ∧
      IsTerminalSep G (A₂ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₂).card
        (L ∩ (A₂ ∪ B)) (X ∩ A₂) (R ∩ (A₂ ∪ B)) ∧
      (X ∩ A₁).card + (X ∩ A₂).card + (X ∩ B).card = X.card := by
  have hp := p3_iff.mp hAB.1
  refine ⟨restr_side G A₁ B ?_ L X R hLXR, restr_side G A₂ B ?_ L X R hLXR, ?_⟩
  · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := hp v
    tauto
  · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := hp v
    tauto
  · have e : X = (X ∩ A₁) ∪ (X ∩ A₂) ∪ (X ∩ B) := by
      ext v
      have := hp v
      simp only [Finset.mem_univ, iff_true] at this
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have d1 : Disjoint (X ∩ A₁) (X ∩ A₂) := by
      refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      have := hp v
      simp only [Finset.mem_inter] at h1 h2
      tauto
    have d2 : Disjoint ((X ∩ A₁) ∪ (X ∩ A₂)) (X ∩ B) := by
      refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      have := hp v
      simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
      tauto
    have h := congrArg Finset.card e
    rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1] at h
    omega
