-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalRelevant_X_mem_ker_iff_e50bcbd76c39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:24.821767+00:00
-- url     : https://prove2.me/submissions/c6bd0a1c-6324-43d7-8ab9-9bcd571688f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRelevant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
theorem _root_.solution {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ)
    (p : Σ k, ι k) :
    (X p : MvPolynomial (Σ k, ι k) ℤ) ∈ RingHom.ker (T.multiConeMap c) ↔ c p = 0 := by
  rw [RingHom.mem_ker]
  unfold T.multiConeMap
  rw [eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]
end GroundTheory.Heights₂.Heights.Inter.DiagonalRelevant
