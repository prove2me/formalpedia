-- Prove2me | solution 1 for acyclic_orientation_maximal_unwinnable_correspondence_and_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:56:15.03159+00:00
-- url     : https://prove2.me/submissions/9dc1574e-00bd-4efb-8977-4f5624dd7024

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_maximal_unwinnable_deg
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_orientation_determined_by_indegrees
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution
    {G : CFGraph} (h_conn : graph_connected G) (q : G.V) :
    (Function.Injective (λ (O : {O : CFOrientation G // is_acyclic G O ∧ is_source G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv G, maximal_unwinnable G D → deg D = genus G - 1) := by
  constructor
  { -- Part 1: Injection proof
    intros O₁ O₂ h_eq
    have h_indeg : ∀ v : G.V, indeg G O₁.val v = indeg G O₂.val v := by
      intro v
      have := congr_fun h_eq v
      by_cases hv : v = q
      · have h₁ := O₁.prop.2; have h₂ := O₂.prop.2
        dsimp only [is_source] at h₁ h₂
        rw [hv, h₁, h₂]
      · simp only [hv, ↓reduceIte, tsub_zero] at this
        exact this
    exact Subtype.ext (orientation_determined_by_indegrees O₁.val O₂.val O₁.prop.1 O₂.prop.1 h_indeg)
  }
  { -- Part 2: Degree characterization
    -- This now correctly refers to the theorem defined above
    intro D hD
    exact maximal_unwinnable_deg h_conn D hD
  }
