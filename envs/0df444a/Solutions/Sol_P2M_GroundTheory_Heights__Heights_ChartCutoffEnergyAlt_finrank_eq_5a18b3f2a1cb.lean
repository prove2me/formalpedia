-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_finrank_eq_5a18b3f2a1cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:33.933715+00:00
-- url     : https://prove2.me/submissions/f05e9c2c-c692-49d8-b1c5-ecba37700eaf

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution (n : ℕ) : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * n + 2 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
