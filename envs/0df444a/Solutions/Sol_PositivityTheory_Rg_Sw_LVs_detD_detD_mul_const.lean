-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.detD_detD_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:50.511811+00:00
-- url     : https://prove2.me/submissions/d5d32198-1313-4ea7-8a14-55951e6302dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iteratedFDeriv_mul_const_of
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_detD_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by
  rw [detD_detD_comp (fun y => F y * c) U hU (hF.mul contDiffOn_const) x₀ hx LA LB,
    detD_detD_comp F U hU hF x₀ hx LA LB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [iteratedFDeriv_mul_const_of F U hU hF c x₀ hx]; ring
end PositivityTheory.Rg.Sw.LVs
