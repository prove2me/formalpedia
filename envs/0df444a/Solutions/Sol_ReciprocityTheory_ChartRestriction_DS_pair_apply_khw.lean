-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.pair_apply_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:48.624995+00:00
-- url     : https://prove2.me/submissions/4bbfd6fb-4de9-4fec-a8bc-3dfcb228846c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ W} {μ : Fin n → ℝ} {v : W} {a b : Fin n}
    (hc : E a b * E b a - E b a * E a b = E a a - E b b) (hd : ∀ a, E a a v = (μ a : ℂ) • v)
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  unfold hwTerm
  rcases lt_trichotomy a b with h | rfl | h
  · have hc' : E a b * E b a = E b a * E a b + (E a a - E b b) := by
      rw [← hc]; abel
    rw [hc']
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, hab h, map_zero,
      hd, zero_add, if_neg h.ne, if_pos h]
    push_cast
    rw [sub_smul]
  · simp only [Module.End.mul_apply, hd, map_smul, smul_smul, if_true]
    push_cast; ring_nf
  · simp [Module.End.mul_apply, hba h, h.ne', not_lt_of_gt h]
end ReciprocityTheory.ChartRestriction.DS
