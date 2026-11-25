-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_d_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:35.773725+00:00
-- url     : https://prove2.me/submissions/d60cf16b-3e14-4229-a85b-2da69b258646

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_d_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_db_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (η : M → ℝ) (U : Set M) (hU : IsOpen U)
    (hη : ∀ y ∈ U, η y = 1) (x : M) (hx : x ∈ U) :
    d n z j (fun y => (η y : ℂ)) x = 0 ∧ db n z j (fun y => (η y : ℂ)) x = 0 := by
  have hev : (fun y => (η y : ℂ)) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hη y hy]
  rw [cut_d_congr n z hz j _ _ x hev, cut_db_congr n z hz j _ _ x hev]
  constructor
  · unfold d
    split_ifs
    · simp [wd, Function.comp_def]
    · rfl
  · unfold db
    split_ifs
    · simp [wdb, Function.comp_def]
    · rfl
end ReciprocityTheory.L2DbarEstimates.F
