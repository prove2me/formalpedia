-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.iterated_fderiv_right_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:47.963028+00:00
-- url     : https://prove2.me/submissions/80271b80-b1dd-4845-b57e-8ed9494c49ff

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mulR_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) := by
  classical
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ N F) x :=
    hFx.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top N)
  have hg : ∀ i : Fin N, HasFDerivAt (fun y : M2 n => y * W i.succ) (mulR (W i.succ)) x :=
    fun i => (mulR (W i.succ)).hasFDerivAt
  have h := hd.hasFDerivAt.continuousMultilinearMap_apply (g := fun i y => y * W i.succ) hg
  have hz : ∀ i : Fin N, mulR (W i.succ) (x * W 0) = 0 := fun i => by
    rw [mulR_apply, mul_assoc, hW, mul_zero]
  refine (congrArg (fun L => L (x * W 0)) h.fderiv).trans ?_
  have hs : ∀ L : Fin N → (M2 n →L[ℂ] ℂ), (∀ i, L i (x * W 0) = 0) → (∑ i, L i) (x * W 0) = 0 := by
    intro L hL
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hL i
  rw [ContinuousLinearMap.add_apply, hs _ (fun i => by rw [ContinuousLinearMap.comp_apply, hz, map_zero]), add_zero,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
  rfl
end PositivityTheory.Rg.Sw.LVs
