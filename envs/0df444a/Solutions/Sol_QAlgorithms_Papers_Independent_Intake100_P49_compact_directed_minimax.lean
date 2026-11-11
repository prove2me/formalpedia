-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P49.compact_directed_minimax
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:29:21.757491+00:00
-- url     : https://prove2.me/submissions/be2de2d3-6b9c-43d3-8eaf-e24775a3c567

import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

open Set

/-- An upper semicontinuous extended-real function on a nonempty compact space
attains its supremum, including either infinite endpoint. -/
private theorem exists_eq_iSup_of_upperSemicontinuous
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (g : X → EReal) (hg : UpperSemicontinuous g) :
    ∃ x, g x = ⨆ z, g z := by
  obtain ⟨x, _, hx⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (s := Set.univ) Set.univ_nonempty isCompact_univ (hg.upperSemicontinuousOn Set.univ)
  refine ⟨x, le_antisymm (le_iSup g x) (iSup_le fun z => ?_)⟩
  exact hx (Set.mem_univ z)

/-- Compact-directed extended minimax with all maxima attained. -/
theorem solution {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [PartialOrder Y] [Nonempty Y] [IsDirectedOrder Y]
    (f : X → Y → EReal)
    (husc : ∀ y, UpperSemicontinuous (fun x => f x y)) (hanti : ∀ x, Antitone (f x)) :
    (⨆ x, ⨅ y, f x y) = (⨅ y, ⨆ x, f x y) ∧
    (∀ y, ∃ x, f x y = ⨆ x, f x y) ∧
    (∃ x, (⨅ y, f x y) = ⨆ x, ⨅ y, f x y) := by
  have hmax : ∀ y, ∃ x, f x y = ⨆ z, f z y :=
    fun y => exists_eq_iSup_of_upperSemicontinuous (fun x => f x y) (husc y)
  let b : EReal := ⨅ y, ⨆ x, f x y
  let C : Y → Set X := fun y => {x | b ≤ f x y}
  have hclosed : ∀ y, IsClosed (C y) := fun y => (husc y).isClosed_preimage b
  have hnonempty : ∀ y, (C y).Nonempty := by
    intro y
    obtain ⟨x, hx⟩ := hmax y
    refine ⟨x, ?_⟩
    show b ≤ f x y
    rw [hx]
    exact iInf_le (fun y => ⨆ x, f x y) y
  have hdir : Directed (· ⊇ ·) C := by
    intro y₁ y₂
    obtain ⟨z, hy₁, hy₂⟩ := exists_ge_ge y₁ y₂
    refine ⟨z, ?_, ?_⟩
    · intro x hx
      exact le_trans hx (hanti x hy₁)
    · intro x hx
      exact le_trans hx (hanti x hy₂)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hdir hnonempty (fun y => (hclosed y).isCompact) hclosed
  have hbound : b ≤ ⨅ y, f x y := by
    apply le_iInf
    intro y
    exact Set.mem_iInter.mp hx y
  refine ⟨le_antisymm (iSup_iInf_le_iInf_iSup f)
    (le_trans hbound (le_iSup (fun x => ⨅ y, f x y) x)), hmax, ?_⟩
  exact exists_eq_iSup_of_upperSemicontinuous
    (fun x => ⨅ y, f x y) (upperSemicontinuous_iInf husc)

#print axioms solution
