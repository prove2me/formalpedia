-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_update_comp_swap_bf4bc8283636
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:19.841863+00:00
-- url     : https://prove2.me/submissions/e4f98875-120c-4eb7-9654-d2337fc0b1fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySymm

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySymmetry
namespace GroundTheory.Heights₂.Heights.ChartEnergySymmetry
theorem _root_.solution {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'
end GroundTheory.Heights₂.Heights.ChartEnergySymmetry
