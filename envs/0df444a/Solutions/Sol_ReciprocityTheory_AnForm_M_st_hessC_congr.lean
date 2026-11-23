-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_hessC_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:35.356535+00:00
-- url     : https://prove2.me/submissions/fefd2ad0-95bb-4729-b0d8-f7d1584d01bc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y :=
    (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold hessC
  rw [h2]
end ReciprocityTheory.AnForm.M
