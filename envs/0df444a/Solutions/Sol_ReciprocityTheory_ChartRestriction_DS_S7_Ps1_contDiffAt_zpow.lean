-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.contDiffAt_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:58.279346+00:00
-- url     : https://prove2.me/submissions/54e30f31-6a9a-4cf2-ad76-6735ca77f9ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP

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
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution {f : 𝕄 → ℂ} {x : 𝕄}
    (hf : ContDiffAt ℂ 1 f x) (hx : f x ≠ 0) (m : ℤ) : ContDiffAt ℂ 1 (fun y => f y ^ m) x := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa only [zpow_natCast] using hf.pow k
  · refine ((hf.pow k).inv (pow_ne_zero k hx)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [_root_.zpow_neg]
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
