-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:02.594206+00:00
-- url     : https://prove2.me/submissions/17ad891c-53d3-4996-baaa-b323d8e4e190

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {D : ℕ} {U V : Set (Fin D → ℂ)} {u : (Fin D → ℂ) → ℝ} (h : IsPsh U u)
    (hVU : V ⊆ U) : IsPsh V u :=
  ⟨h.1.mono hVU, fun z w hz => h.2 z w fun ζ hζ => hVU (hz ζ hζ)⟩
end GroundTheory.Heights₂.Heights.Regular
