-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.localExtension_eq_mul_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:21.343478+00:00
-- url     : https://prove2.me/submissions/0a5157b3-5836-4531-98a2-22473688e124

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_not_mem_neighborhood_of_ne

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hL : IsLocalData n g ph r W m) (hfin : (zeroSet n g).Finite)
    {p x : M} (hp : p ∈ zeroSet n g) (hx : x ∈ W p) :
    gt n z g c W x = c p * jac n z g x := by
  unfold gt
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_eq_single p (fun q hq hqp => Set.indicator_of_notMem
      (not_mem_neighborhood_of_ne n g ph r W m hL hp ((hfin.mem_toFinset).1 hq) hqp hx) _)
      (fun h => absurd ((hfin.mem_toFinset).2 hp) h), Set.indicator_of_mem hx]
end ReciprocityTheory.L2DbarEstimates.I
