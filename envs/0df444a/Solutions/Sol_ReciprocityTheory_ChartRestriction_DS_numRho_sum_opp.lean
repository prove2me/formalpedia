-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.numRho_sum_opp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:35.79223+00:00
-- url     : https://prove2.me/submissions/34f2e93d-e2d9-4c13-8777-ef9fb32735e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho

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
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) :
    (∑ a, ((univ.filter fun c => ε c ≠ ε a).card : ℝ)) = 2 * (pOf ε : ℝ) * (qOf ε : ℝ) := by
  have h1 : ∀ a : Fin n, ((univ.filter fun c => ε c ≠ ε a).card : ℝ) =
      if ε a = true then (qOf ε : ℝ) else (pOf ε : ℝ) := by
    intro a
    cases h : ε a <;> simp [pOf, qOf]
  have hq : (univ.filter fun x => ¬ ε x = true).card = qOf ε := by simp [qOf]
  have hp : (univ.filter fun x => ε x = true).card = pOf ε := rfl
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    hq, hp]
  simp only [nsmul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.DS
