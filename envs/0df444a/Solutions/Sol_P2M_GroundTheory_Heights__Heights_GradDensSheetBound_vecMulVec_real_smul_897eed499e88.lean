-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_vecMulVec_real_smul_897eed499e88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:22.884769+00:00
-- url     : https://prove2.me/submissions/a0f0f038-5d84-44cb-8fb9-fb94fa60a8ce

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound

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
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {m : ℕ} (r r' : ℝ) (a b : Fin m → ℂ) :
    vecMulVec ((r : ℂ) • a) (star ((r' : ℂ) • b)) = ((r * r' : ℝ) : ℂ) • vecMulVec a (star b) := by
  ext j k
  simp [vecMulVec_apply]
  ring
end GroundTheory.Heights₂.Heights.GradDensSheetBound
