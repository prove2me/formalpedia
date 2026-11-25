-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_dz_cplx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:07.853797+00:00
-- url     : https://prove2.me/submissions/36053d4a-1e9e-4a92-92a2-e3850f0e3b9c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_fderiv_cplx

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
    (hf : HasFDerivAt f L y) (j : Fin D) :
    dz j (cplx f) y = (((L (Pi.single j 1) : ℝ) : ℂ) -
      Complex.I * ((L (Complex.I • Pi.single j 1) : ℝ) : ℂ)) / 2 := by
  simp only [dz, st_fderiv_cplx hf]
end ReciprocityTheory.AnForm.M
