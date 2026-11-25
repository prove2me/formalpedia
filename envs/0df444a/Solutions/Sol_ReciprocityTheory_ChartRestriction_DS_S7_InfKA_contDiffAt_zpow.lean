-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.contDiffAt_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:38.946049+00:00
-- url     : https://prove2.me/submissions/69469aa2-48ab-4d1f-8123-721bf44037a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM

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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiffAt ℂ 1 f x) (hx : f x ≠ 0) (m : ℤ) : ContDiffAt ℂ 1 (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    have e : (fun y => f y ^ (Int.ofNat k)) = fun y => f y ^ k :=
      funext fun y => by rw [Int.ofNat_eq_coe, zpow_natCast]
    rw [e]
    exact hf.pow k
  | negSucc k =>
    have e : (fun y => f y ^ (Int.negSucc k)) = fun y => (f y ^ (k + 1))⁻¹ :=
      funext fun y => zpow_negSucc _ _
    rw [e]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
