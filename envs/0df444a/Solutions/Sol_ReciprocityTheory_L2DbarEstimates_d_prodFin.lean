-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.d_prodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:00.944991+00:00
-- url     : https://prove2.me/submissions/f6299dbd-0cf1-4c8e-a8aa-ff86a08011f2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    d n (fun q : M × Fin p => z q.1) j F (x, i) = d n z j (fun y => F (y, i)) x := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [d_eq_wd n _ (chartSlice e i) (isChart_chartSlice n z e he p i) j F (x, i) ⟨hx, rfl⟩,
    d_eq_wd n z e he j _ x hx]
  rfl
end ReciprocityTheory.L2DbarEstimates
