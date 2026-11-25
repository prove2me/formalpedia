-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:13.232807+00:00
-- url     : https://prove2.me/submissions/d24672a4-5d61-428f-b2f0-0cd1011b371d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_homogD_4a39ee24311c
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_eq_zero_of_smul


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z')
    (hz' : z' ∈ ReciprocityTheory.AnForm.R.conePts R.D) : z ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (homogD R) c z' hz'.2⟩
  obtain ⟨i, hi⟩ := hz'.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
