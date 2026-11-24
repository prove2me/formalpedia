-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.detD_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:50.526261+00:00
-- url     : https://prove2.me/submissions/c5f022c5-bfbc-46b7-a7d3-3cef81a912e2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (F : Matrix ι ι ℂ → ℂ) :
    detD (fun S => c * F S) = c * detD F := by
  by_cases hc : c = 0
  · subst hc
    simp [detD]
  · let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc)
    have hfun : (fun S => c * F S) = g ∘ F := by
      funext S
      simp [g, mul_comm]
    unfold detD
    rw [hfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    (simp [g]) <;> ring
end PositivityTheory.Rg.Sw.LVs
