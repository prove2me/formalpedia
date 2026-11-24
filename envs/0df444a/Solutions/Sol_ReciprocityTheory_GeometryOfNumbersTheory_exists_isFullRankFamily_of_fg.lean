-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:57.715824+00:00
-- url     : https://prove2.me/submissions/2dd0184d-649b-4e41-88b1-cc958a0ed1f4

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by
  obtain ⟨S, hS⟩ := hE
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent K (E : Set V)
  have hEle : ∀ x ∈ E, x ∈ Submodule.span K (S : Set V) := by
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ (S : Set V) ?_
    rintro _ ⟨x, rfl⟩
    exact hEle _ (hbE x.2)
  let _ := Fintype.ofFinite b
  refine ⟨Fintype.card b, fun i => ((Fintype.equivFin b).symm i : V), ?_, ?_, ?_⟩
  · intro i; exact hbE ((Fintype.equivFin b).symm i).2
  · exact hli.comp _ (Fintype.equivFin b).symm.injective
  · intro x hx
    have : x ∈ Submodule.span K (b : Set V) := hspan ▸ Submodule.subset_span hx
    have hr : Set.range (fun i => ((Fintype.equivFin b).symm i : V)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin b).symm i).2
      · intro hy; exact ⟨Fintype.equivFin b ⟨y, hy⟩, by simp⟩
    rw [SetLike.mem_coe, hr]
    exact this
end ReciprocityTheory.GeometryOfNumbersTheory
