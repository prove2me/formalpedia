-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:46.33926+00:00
-- url     : https://prove2.me/submissions/fd0fcd2c-eb1f-47a9-96bf-fe07734c7705

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (s : ((k : Unit) → projBlocks K i k) → ℂ) :
    projProj s = ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q) := rfl
end GroundTheory.Heights₂.Heights
