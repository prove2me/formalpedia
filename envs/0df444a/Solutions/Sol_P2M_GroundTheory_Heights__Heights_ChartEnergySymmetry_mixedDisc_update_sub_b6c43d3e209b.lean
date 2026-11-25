-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:18.1138+00:00
-- url     : https://prove2.me/submissions/136ecbef-80ae-4876-ae73-d9ca2837ed92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySymm
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc


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
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]
end GroundTheory.Heights₂.Heights.ChartEnergySymmetry
