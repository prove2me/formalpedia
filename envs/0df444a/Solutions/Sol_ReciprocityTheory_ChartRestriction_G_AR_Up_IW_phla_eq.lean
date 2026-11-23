-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:23.15771+00:00
-- url     : https://prove2.me/submissions/69c3c4c2-6443-486c-a29c-8dcca40c1e61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    phla X la x = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Lm X x τ i.succ - Lm X x τ i.castSucc) := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i => dmin_ne_zero X hx τ i
  have hp : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Real.rpow_pos_of_pos (hp τ i) _).ne')), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hp τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.log_rpow (hp τ i), norm_div,
    Real.log_div (norm_ne_zero_iff.mpr (hd τ _)) (norm_ne_zero_iff.mpr (hd τ _))]
  simp only [Lm]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
