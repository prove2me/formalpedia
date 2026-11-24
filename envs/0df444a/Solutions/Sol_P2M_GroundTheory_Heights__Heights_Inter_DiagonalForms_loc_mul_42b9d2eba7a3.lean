-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_loc_mul_42b9d2eba7a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:23.322491+00:00
-- url     : https://prove2.me/submissions/8760e0a1-9634-4a05-adb7-a4e9e4de6349

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms

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
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution {R : Subalgebra ℤ Ω} {g y z : Ω} (hy : ∃ n : ℕ, g ^ n * y ∈ R)
    (hz : ∃ n : ℕ, g ^ n * z ∈ R) : ∃ n : ℕ, g ^ n * (y * z) ∈ R := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm⟩ := hz
  refine ⟨n + m, ?_⟩
  have : g ^ (n + m) * (y * z) = (g ^ n * y) * (g ^ m * z) := by ring
  rw [this]
  exact mul_mem hn hm
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
