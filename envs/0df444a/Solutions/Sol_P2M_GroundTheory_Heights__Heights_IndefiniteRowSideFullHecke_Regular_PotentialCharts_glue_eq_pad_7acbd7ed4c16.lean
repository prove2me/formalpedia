-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_PotentialCharts_glue_eq_pad_7acbd7ed4c16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:05.1336+00:00
-- url     : https://prove2.me/submissions/f82f74e6-5975-4a53-be3a-4a957601dd92

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regMax_pad_788d5eb1e862
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.PotentialCharts
variable (P : PotentialCharts A)
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.PotentialCharts
theorem _root_.solution (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : X) {c : Fin P.N}
    (hc : x ∈ P.mid c) :
    P.glue a ε x = (haveI : Nonempty (Fin P.N) := ⟨c⟩
      regMax ε (fun j => if x ∈ P.mid j then a j x else a c x - ε)) + ε / 2 := by
  have : Nonempty (Fin P.N) := ⟨c⟩
  rw [PotentialCharts.glue, regMax_pad (fun j => x ∈ P.mid j) (fun j => a j x) hc hε]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.PotentialCharts
