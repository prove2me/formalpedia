-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_hwVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:15.946801+00:00
-- url     : https://prove2.me/submissions/010d393e-b357-42e3-9b77-1fa3f131f52f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_pair_hw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_hwTerm

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
    {v : M} (hv : IsHWVec E μ v) :
    casimir E v = ((nsq (μ + rho n) - nsq (rho n) : ℝ) : ℂ) • v := by
  classical
  have hc : casimir E = ∑ a, ∑ b ∈ univ.filter (fun _ => True), E a b * E b a := by
    simp [casimir]
  have hsum := sum_pair_hw hE (fun _ _ => True) (fun _ _ h => h) hv.1 (fun a b h _ => hv.2 a b h)
  rw [hc, hsum, sum_hwTerm (fun _ _ => True) (fun _ => trivial) (fun _ _ h => h) μ (rho n)]
  intro a
  have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi,
    Fin.card_Iio, rho]
  rw [Nat.sub_sub, Nat.cast_sub ha]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS
