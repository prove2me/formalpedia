-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiffOn_zpow__9c2121c1661f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:14:28.279461+00:00
-- url     : https://prove2.me/submissions/1b9f92ec-5ed8-4386-a643-a170560efb5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℂ ∞ (fun y => f y ^ m) s := by
  rcases m with k | k
  · simpa only [Int.ofNat_eq_coe, zpow_natCast] using hf.pow k
  · refine ((hf.pow (k + 1)).inv (fun x hx => pow_ne_zero _ (h0 x hx))).congr fun x _ => ?_
    exact zpow_negSucc (f x) k
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
