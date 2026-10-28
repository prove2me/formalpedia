-- Prove2me | solution 1 for SetOptLattice.Existence.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:02:09.546993+00:00
-- url     : https://prove2.me/submissions/59391bd4-ae93-4fc3-b5c6-a0e5fcf477d3

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open SetOptLattice.Existence
namespace Aux_SetOptLattice_T42
open SetOptLattice.Existence

theorem anti {Z : Type*} (ψ : Z → EReal) {D E : Set Z} (h : D ⊆ E) :
    infExt ψ E ≤ infExt ψ D := by
  unfold infExt
  exact biInf_mono h

theorem sub_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) : D ⊆ clPsi Ψ D := by
  intro z hz ψ _
  unfold infExt
  exact biInf_le _ hz

theorem inf_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) (ψ : Z → EReal) (hψ : ψ ∈ Ψ) :
    infExt ψ (clPsi Ψ D) = infExt ψ D := by
  apply le_antisymm (anti ψ (sub_cl Ψ D))
  unfold infExt
  exact le_iInf₂ (fun z hz => hz ψ hψ)

theorem eps0 (a : EReal) : epsBound a 0 = a := by
  unfold epsBound
  by_cases ha : a = ⊥
  · rw [if_pos ha, if_pos rfl, ha]
  · rw [if_neg ha]; simp

end Aux_SetOptLattice_T42

open Set Filter Topology
open scoped Pointwise


theorem solution {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x))
    (hlsc : ∀ ψ ∈ Ψ, LowerSemicontinuous (fun x => infExt ψ (f x)))
    (hr : ∀ ψ ∈ Ψ, ∃ r : ℝ, (⨅ x, infExt ψ (f x)) < (r : EReal) ∧
      IsCompact (sublevel (fun x => infExt ψ (f x)) r)) :
    (∀ ψ ∈ Ψ, ∃ xψ : X, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)) ∧
      IsSolution Ψ f 0 {xψ : X | ∃ ψ ∈ Ψ, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)} := by
  open Aux_SetOptLattice_T42 in
  have part1 : ∀ ψ ∈ Ψ, ∃ xψ : X, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x) := by
    intro ψ hψ
    obtain ⟨r, hlt, hcpt⟩ := hr ψ hψ
    obtain ⟨x0, hx0⟩ := iInf_lt_iff.mp hlt
    have hne : (sublevel (fun x => infExt ψ (f x)) r).Nonempty := ⟨x0, le_of_lt hx0⟩
    obtain ⟨a, ha, hmin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne hcpt ((hlsc ψ hψ).lowerSemicontinuousOn _)
    refine ⟨a, le_antisymm (le_iInf (fun y => ?_)) (iInf_le _ a)⟩
    by_cases hy : y ∈ sublevel (fun x => infExt ψ (f x)) r
    · exact isMinOn_iff.mp hmin y hy
    · have ha' : infExt ψ (f a) ≤ (r : EReal) := ha
      have hy' : ¬ infExt ψ (f y) ≤ (r : EReal) := hy
      push_neg at hy'
      exact le_trans ha' hy'.le
  have hU : ∀ ψ : Z → EReal, (⨅ x, infExt ψ (f x)) ≤ infExt ψ (⋃₀ (f '' univ)) := by
    intro ψ
    conv_rhs => unfold infExt
    refine le_iInf₂ (fun z hz => ?_)
    obtain ⟨_, ⟨x, _, rfl⟩, hzx⟩ := hz
    exact le_trans (iInf_le _ x) (by unfold infExt; exact biInf_le _ hzx)
  refine ⟨part1, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨ψ, hψ⟩ := hΨne
    obtain ⟨x, hx⟩ := part1 ψ hψ
    exact ⟨x, ψ, hψ, hx⟩
  · intro ψ hψ
    obtain ⟨x, hx⟩ := part1 ψ hψ
    unfold infImage latInf
    rw [inf_cl Ψ _ ψ hψ, inf_cl Ψ _ ψ hψ, eps0]
    have hsub : f x ⊆ ⋃₀ (f '' {xψ : X | ∃ ψ ∈ Ψ, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)}) :=
      subset_sUnion_of_mem ⟨x, ⟨ψ, hψ, hx⟩, rfl⟩
    calc infExt ψ (⋃₀ (f '' {xψ : X | ∃ ψ ∈ Ψ, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)}))
        ≤ infExt ψ (f x) := anti ψ hsub
      _ = ⨅ x, infExt ψ (f x) := hx
      _ ≤ _ := hU ψ
  · rintro x ⟨ψ, hψ, hx⟩
    refine ⟨ψ, hψ, ?_⟩
    unfold infImage latInf
    rw [inf_cl Ψ _ ψ hψ, eps0, hx]
    exact hU ψ
