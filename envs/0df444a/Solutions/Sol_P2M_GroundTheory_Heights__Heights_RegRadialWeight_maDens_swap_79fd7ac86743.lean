-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_swap_79fd7ac86743
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:50.563119+00:00
-- url     : https://prove2.me/submissions/0f280cf5-fbe5-469d-857b-da6a50d0c48b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegRadialWeight
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_comp_perm


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
open GroundTheory.Heights₂.Heights.RegRadialWeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RegRadialWeight
theorem _root_.solution {e : ℕ} (X G : (Fin (e + 1 + 1) → ℂ) → ℝ) (z : Fin (e + 1 + 1) → ℂ) :
    maDens (Fin.cons X (Fin.cons G fun _ : Fin e => X)) z = maDens (Fin.cons G fun _ : Fin (e + 1) => X) z := by
  have h : (fun k => hessC ((Fin.cons X (Fin.cons G fun _ : Fin e => X) : Fin (e + 1 + 1) → _) k) z) =
      (fun k => hessC ((Fin.cons G fun _ : Fin (e + 1) => X : Fin (e + 1 + 1) → _) k) z) ∘
        Equiv.swap 0 1 := by
    funext k
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k
    · simp [Equiv.swap_apply_left]
    · simp [Equiv.swap_apply_right]
    · have h0 : (j.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (j.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        intro h; exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  unfold maDens
  rw [h, mdisc_comp_perm]
end GroundTheory.Heights₂.Heights.RegRadialWeight
