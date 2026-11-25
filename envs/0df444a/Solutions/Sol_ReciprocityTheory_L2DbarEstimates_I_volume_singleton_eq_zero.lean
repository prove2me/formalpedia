-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.volume_singleton_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:46.829365+00:00
-- url     : https://prove2.me/submissions/2fdb96b3-45c6-4cad-826c-7629423c1ce6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_injOn_source_of_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (hn : 1 ≤ n) (z : M → V n)
    (hz : IsLocalHomeomorph z) (p : M) : vol n z {p} = 0 := by
  obtain ⟨e, he, hp⟩ := exists_chart n z hz p
  rw [vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) {p}
    (measurableSet_singleton p) (Set.singleton_subset_iff.2 hp), Set.image_singleton]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact measure_singleton _
end ReciprocityTheory.L2DbarEstimates.I
