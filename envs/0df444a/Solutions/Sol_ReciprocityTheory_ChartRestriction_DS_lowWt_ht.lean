-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWt_ht
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:42.949385+00:00
-- url     : https://prove2.me/submissions/758f36ca-b1e7-461c-a3c9-cd9328f955ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) →
      (∑ i : Fin n, ((i : ℕ) : ℝ) * μ i) + l.length ≤ ∑ i : Fin n, ((i : ℕ) : ℝ) * lowWt μ l i
  | [], _ => by simp [lowWt]
  | p :: l, hl => by
    have ih := solution μ l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := (hl p (List.mem_cons_self ..)).1
    have hr : ∑ i : Fin n, ((i : ℕ) : ℝ) * root p.1 p.2 i = (p.1 : ℝ) - (p.2 : ℝ) := by
      simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    have hlt : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp
    simp only [lowWt, Pi.add_apply, mul_add, Finset.sum_add_distrib, hr, List.length_cons]
    push_cast
    linarith
end ReciprocityTheory.ChartRestriction.DS
