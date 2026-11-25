-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.line_hasFDerivAt_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:41.530174+00:00
-- url     : https://prove2.me/submissions/ec464543-f645-4de5-b84c-2a8045f89f53

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasFDerivAt_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (Gc φ z w) (Hc φ z w ζ) ζ := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z + ζ • w)) (z + ζ • w) :=
    ((h2.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  exact (Pc w).hasFDerivAt.comp ζ (hd.comp ζ (hasFDerivAt_line z w ζ))
end ReciprocityTheory.AnForm.A.PshLap
