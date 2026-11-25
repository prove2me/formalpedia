-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.pair_apply_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:43.781551+00:00
-- url     : https://prove2.me/submissions/05a75727-b0c4-47eb-89c5-9a9149f80dba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hd : ∀ a, E a a v = (μ a : ℂ) • v) {a b : Fin n}
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  rcases lt_trichotomy a b with h | rfl | h
  ·
    have hc := congrArg (fun f : Module.End ℂ M => f v) (hE a b b a)
    simp only [if_pos rfl, if_true, ite_true, LinearMap.sub_apply, Module.End.mul_apply, hab h, map_zero,
      sub_zero] at hc
    rw [Module.End.mul_apply, hc, hd, hd]
    simp [hwTerm, h, h.ne, sub_smul]
  · rw [Module.End.mul_apply, hd, map_smul, hd, smul_smul]
    simp [hwTerm]
  · rw [Module.End.mul_apply, hba h, map_zero]
    simp [hwTerm, h.ne', not_lt.2 h.le]
end ReciprocityTheory.ChartRestriction.DS
