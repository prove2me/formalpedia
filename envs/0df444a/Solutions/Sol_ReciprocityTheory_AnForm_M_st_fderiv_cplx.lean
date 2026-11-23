-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_fderiv_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:34.793803+00:00
-- url     : https://prove2.me/submissions/ff90c34f-1113-45d6-9928-b4066f34a4ea

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD

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
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {L : (Fin D → ℂ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L y) (d : Fin D → ℂ) :
    fderiv ℝ (cplx f) y d = ((L d : ℝ) : ℂ) := by
  have h : HasFDerivAt (cplx f) (Complex.ofRealCLM.comp L) y := by
    unfold cplx
    exact Complex.ofRealCLM.hasFDerivAt.comp y hf
  rw [h.fderiv]
  simp
end ReciprocityTheory.AnForm.M
