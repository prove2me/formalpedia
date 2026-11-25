-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:31.69392+00:00
-- url     : https://prove2.me/submissions/c6570eb4-6aea-4dfa-9ced-eae27d69c499

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.Conservation
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by
  intro h
  have : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr h
  rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP, Ideal.mem_bot] at this
  exact ha this
end GroundTheory.Heights₂.Heights.Inter.Conservation
