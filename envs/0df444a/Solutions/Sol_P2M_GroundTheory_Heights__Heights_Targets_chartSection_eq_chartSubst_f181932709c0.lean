-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_chartSection_eq_chartSubst_f181932709c0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:54.272467+00:00
-- url     : https://prove2.me/submissions/b9fc763d-921e-4cee-9f4c-8a11963d0054

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) :
    chartSection σ i s = chartSubst σ i (map (Int.castRingHom ℂ) s) := rfl
end GroundTheory.Heights₂.Heights.Targets
