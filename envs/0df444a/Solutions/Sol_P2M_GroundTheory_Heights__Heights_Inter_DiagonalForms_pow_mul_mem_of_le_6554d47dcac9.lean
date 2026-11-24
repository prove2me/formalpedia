-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_pow_mul_mem_of_le_6554d47dcac9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:42.819161+00:00
-- url     : https://prove2.me/submissions/37ed0342-9897-4ba0-a511-e199fb47b1d4

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
theorem _root_.solution {R : Subalgebra ℤ Ω} {g y : Ω} (hg : g ∈ R) {n N : ℕ} (hn : n ≤ N)
    (h : g ^ n * y ∈ R) : g ^ N * y ∈ R := by
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  exact mul_mem (pow_mem hg _) h
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
