-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptGood_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:32.767682+00:00
-- url     : https://prove2.me/submissions/44cf5a23-4e16-4318-83ca-f7c6d3416afe

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {ι τ : Type*} {T : (ι → MvPowerSeries τ C) → (ι → MvPowerSeries τ C)}
    (hP : ∀ n, PTGood v (T^[n] 0)) (x : ι → MvPowerSeries τ C)
    (hx : ∀ n, PTAgree n x (T^[n] 0)) : PTGood v x := by
  intro i
  have hc : ∀ e, coeff e (x i) = coeff e ((T^[e.degree + 1] 0) i) :=
    fun e => hx (e.degree + 1) i e (Nat.lt_succ_self _)
  refine ⟨?_, ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hP _ i).1
  · show ∀ α, coeff α (x i) ∈ ptIntSub v
    intro α
    have h : ∀ β, coeff β ((T^[α.degree + 1] 0) i) ∈ ptIntSub v := (hP _ i).2
    rw [hc]
    exact h α
end ReciprocityTheory.ChartRestriction.G.Sh
