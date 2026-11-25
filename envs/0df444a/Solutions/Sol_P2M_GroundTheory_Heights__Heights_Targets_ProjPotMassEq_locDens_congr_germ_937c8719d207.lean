-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_locDens_congr_germ_937c8719d207
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:34.275372+00:00
-- url     : https://prove2.me/submissions/5b4f589e-3aae-4410-ba27-47a4ce3d742f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDens_congr


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
theorem _root_.solution (A : FinHolAtlas e X) (P Q : LocPot X) (j : Fin A.n) (y : Fin e → ℂ)
    (h : (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    locDens A (fun _ => P) j y = locDens A (fun _ => Q) j y :=
  ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun _ => h
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
