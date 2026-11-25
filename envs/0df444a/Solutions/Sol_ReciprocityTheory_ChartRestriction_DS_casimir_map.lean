-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:31.017507+00:00
-- url     : https://prove2.me/submissions/254ea723-2b27-457a-b435-7fef3f62ae5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (x : M) :
    f (casimir E x) = casimir E' (f x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hf]
end ReciprocityTheory.ChartRestriction.DS
