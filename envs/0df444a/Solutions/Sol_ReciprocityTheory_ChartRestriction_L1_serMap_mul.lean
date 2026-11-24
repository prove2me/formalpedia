-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.serMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:21.31558+00:00
-- url     : https://prove2.me/submissions/ef1305e5-66b2-4bcb-a5bf-eed36d1b282b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_serMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {E : Type} [Field E]
variable (k : Subfield E)
variable {k}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]
end ReciprocityTheory.ChartRestriction.L1
