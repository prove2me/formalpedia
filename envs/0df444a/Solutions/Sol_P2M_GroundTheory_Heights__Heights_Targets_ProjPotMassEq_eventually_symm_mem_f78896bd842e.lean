-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:59.858108+00:00
-- url     : https://prove2.me/submissions/7f1e0d2a-be5f-4772-a946-9d56913d9409

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {S : Set X} (hS : IsOpen S) (hyS : (A.chart j).symm y ∈ S) :
    ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ S :=
  ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hS.mem_nhds hyS)
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
