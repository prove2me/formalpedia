-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:35.501098+00:00
-- url     : https://prove2.me/submissions/48f387ae-f7ef-4532-a43d-44baf9209183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts

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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => T.op (k * γ t)) (T.op k * T.dτ Y) 0 := by
  have h1 := T.hasDeriv Y hY γ hγ
  have e : (fun t => T.op (k * γ t)) = fun t => T.op k * T.op (γ t) := by
    funext t
    exact congrArg Subtype.val (map_mul T.τ k (γ t))
  rw [e]
  exact h1.const_mul (T.op k)
end ReciprocityTheory.ChartRestriction.DS.S7
