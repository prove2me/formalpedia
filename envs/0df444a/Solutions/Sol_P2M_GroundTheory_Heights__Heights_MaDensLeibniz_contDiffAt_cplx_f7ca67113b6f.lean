-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:42.078085+00:00
-- url     : https://prove2.me/submissions/d94dc2c9-f550-4a84-8c12-e89111775aa9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz

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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLeibniz
theorem _root_.solution {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by
  have h : cplx f = fun y => Complex.ofRealCLM (f y) := by funext y; simp [cplx]
  rw [h]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
end GroundTheory.Heights₂.Heights.MaDensLeibniz
