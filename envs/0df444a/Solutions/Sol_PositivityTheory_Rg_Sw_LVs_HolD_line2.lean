-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolD.line2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:33.393193+00:00
-- url     : https://prove2.me/submissions/cabb48f9-cc83-4106-be8b-2a9427bea5e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Theorems.Thm_GlobalTheory_SCV_fderiv_apply_eq_zero_of_frequently
import Theorems.Thm_GlobalTheory_SCV_frequently_nhdsNE_of_eventually_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolD
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.HolD
theorem _root_.solution {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h
end PositivityTheory.Rg.Sw.LVs.HolD
