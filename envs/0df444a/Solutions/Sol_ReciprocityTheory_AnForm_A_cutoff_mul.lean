-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.cutoff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:48.812234+00:00
-- url     : https://prove2.me/submissions/0ae2cc27-d8e1-4396-a899-ab4827d13579

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {χ φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hts : tsupport χ ⊆ U) (hφ : ContDiffOn ℝ 3 φ U) :
    ContDiff ℝ 3 (fun x => χ x * φ x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (contDiff_infty.1 hχ 3).contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hts h)
    have h0 : (fun x => χ x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0
end ReciprocityTheory.AnForm.A
