-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.integral_radialBump_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:16.50014+00:00
-- url     : https://prove2.me/submissions/28fd6b5b-3474-43db-b2db-4d8a3a3dd7f2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_hasCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshMol
theorem _root_.solution (D : ℕ) : 0 < ∫ w, g0 D w :=
  (radialBump_contDiff D).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (radialBump_hasCompactSupport D)
    (radialBump_nonneg D) (by
      rw [g0, b0.one_of_mem_closedBall]
      · norm_num
      · simp [b0])
end ReciprocityTheory.AnForm.A.PshMol
