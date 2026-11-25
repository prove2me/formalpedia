-- Prove2me | solution 1 for P2M_GlobalTheory_SharpGradient_sharpAt_sum__57325bd9992d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:03.913933+00:00
-- url     : https://prove2.me/submissions/32f2826c-df02-4fdd-9511-f44932f9e042

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_sharpAt_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.SharpGradient
theorem _root_.solution {ι : Type} [Fintype ι] {u : ι → V n → ℝ} {x : V n} {ξ : Fin n → ℂ}
    (h : ∀ i, SharpAt (u i) x ξ) : SharpAt (fun y => ∑ i, u i y) x ξ := by
  have e : (fun y => ∑ i, u i y) = fun y => ∑ k, u ((Fintype.equivFin ι).symm k) y := by
    funext y
    exact ((Fintype.equivFin ι).symm.sum_comp (fun i => u i y)).symm
  rw [e]
  exact sharpAt_sum fun k => h _
end GlobalTheory.SharpGradient
