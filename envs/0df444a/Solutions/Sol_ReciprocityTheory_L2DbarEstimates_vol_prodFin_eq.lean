-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.vol_prodFin_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:59.937553+00:00
-- url     : https://prove2.me/submissions/02b73cfa-b187-4db5-93c4-b59405f109a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_volFun_prod_singleton
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_apply


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i, (vol n z).map (fun x => (x, i)) := by
  ext A hA
  have hz' := isLocalHomeomorph_comp_fst n z hz p
  have hS : ∀ i : Fin p, MeasurableSet ((fun x => (x, i)) ⁻¹' A) := fun i =>
    (measurable_id.prodMk measurable_const) hA
  have hA' : A = ⋃ i : Fin p, ((fun x => (x, i)) ⁻¹' A) ×ˢ {i} := by
    ext ⟨x, j⟩
    simp
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  conv_lhs => rw [hA']
  rw [measure_iUnion (fun i j hij => Set.disjoint_left.2 fun q hq1 hq2 => hij (hq1.2.symm.trans hq2.2))
    (fun i => (hS i).prod (measurableSet_singleton i)), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (f := fun x => (x, i)) (measurable_id.prodMk measurable_const) hA,
    vol_apply n _ hz' _ ((hS i).prod (measurableSet_singleton i)), volFun_prod_singleton,
    vol_apply n z hz _ (hS i)]
end ReciprocityTheory.L2DbarEstimates
