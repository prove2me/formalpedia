-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylSum_pIdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:08.067681+00:00
-- url     : https://prove2.me/submissions/0d15f08c-8d65-4bf3-a8c7-dfff3c787d63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylSum

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (β : Bool) (F G : Fin n → ℝ) :
    ∑ p : pIdx ε β, F p.1.1 * G p.1.2 =
      (∑ i ∈ univ.filter (fun i => ε i = β), F i) * ∑ j ∈ univ.filter (fun j => ε j = !β), G j := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.filter_product, Finset.univ_product_univ]
  exact (Finset.sum_subtype _ (by simp) (fun q : Fin n × Fin n => F q.1 * G q.2)).symm
end ReciprocityTheory.ChartRestriction.DS.HW
