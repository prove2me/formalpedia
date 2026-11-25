-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefIntCpt_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:50.815968+00:00
-- url     : https://prove2.me/submissions/0158f2bd-a5db-4398-956b-5bccf4986604

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntCpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hq : S7.q0 ε = 0) (g : S7.UJ ε) :
    (S7.toM g)ᴴ * S7.toM g = 1 := by
  have h1 : inUJ ε (S7.toM g) := g.2
  unfold inUJ at h1
  unfold S7.q0 pOf qOf at hq
  rcases Nat.min_eq_zero_iff.mp hq with h0 | h0
  · have hf : ∀ a, ε a = false := fun a => by
      simpa using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) (Finset.mem_univ a)
    have hJ : Jm ε = -1 := by
      ext i j
      by_cases h : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, h, hf]
    rw [hJ] at h1
    simpa using h1
  · have hf : ∀ a, ε a = true := fun a => by
      simpa using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) (Finset.mem_univ a)
    have hJ : Jm ε = 1 := by
      ext i j
      by_cases h : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, h, hf]
    rw [hJ] at h1
    simpa using h1
end ReciprocityTheory.ChartRestriction.DS
