-- Prove2me | solution 1 for P2M_GlobalTheory_LeviZero_leviV_sum__12cf4af592ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:37.06935+00:00
-- url     : https://prove2.me/submissions/df240004-db45-4c1b-a150-4493dcd65fc2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}
namespace GlobalTheory.LeviZero
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ}
    (h : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    leviV n (fun y => ∑ i ∈ s, f i y) x ξ = ∑ i ∈ s, leviV n (f i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using leviV_const' 0 x ξ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [leviV_add' (h i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
end GlobalTheory.LeviZero
