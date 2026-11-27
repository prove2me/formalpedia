-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_exists_chart_69e894168a06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:29.663326+00:00
-- url     : https://prove2.me/submissions/2e80efaa-cbe5-4f04-8efd-5cbcf856f8e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩
end GroundTheory.Heights₂.Heights.Targets
