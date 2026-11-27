-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_cuspWeight_gauss_0ce6fe17e050
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:07.252585+00:00
-- url     : https://prove2.me/submissions/fb6ef7a9-c803-43a0-b7c9-f86f14f5ea97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
open GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open GaussianInt
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (II : IntersectionSystem) (hII) (z : (Σ _ : Unit, Fin 2) → ℂ) :
    (gaussCusp II hII).cuspWeight z = 0 := by
  have : {x | ∃ I : Submodule GaussianInt GaussianInt, I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub (gaussCusp II hII).form I ∧ x = -Real.log ((gaussCusp II hII).Nz z I)} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro I hI _ hiso _
    exact hI ((Submodule.eq_bot_iff I).2 fun v hv => eq_zero_of_isIsoSub hiso hv)
  rw [CuspData.cuspWeight, this, Real.sSup_empty, max_self]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
