-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_maDens_cons_eq_zero_7292b531e842
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:00.590609+00:00
-- url     : https://prove2.me/submissions/143550fe-2e37-4da1-a83a-d841258be50b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessCGerm


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffBoundaryBound
theorem _root_.solution {D : ℕ} (f : (Fin (D + 1) → ℂ) → ℝ) (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : f =ᶠ[𝓝 y] fun _ => 0) : maDens (Fin.cons f ψ) y = 0 := by
  have h0 : hessC f y = ((0 : ℝ) : ℂ) • hessC (fun _ => (0 : ℝ)) y := by
    rw [ReciprocityTheory.AnForm.M.hessCGerm f _ y h]
    ext i j
    simp [hessC]
  rw [maDens_cons_of_hessC_eq_smul f (fun _ => 0) ψ y 0 h0, zero_mul]
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
