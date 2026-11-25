-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:41.35004+00:00
-- url     : https://prove2.me/submissions/4330b4b5-deae-4495-893f-db60ca6e32dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiffOn ℂ ω f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℂ ω (fun x => f x ^ m) s := by
  rcases m with k | k
  · simpa using hf.pow k
  · have h1 := (hf.pow (k + 1)).inv (fun x hx => pow_ne_zero _ (h0 x hx))
    refine h1.congr fun x _ => ?_
    simp [zpow_negSucc]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
