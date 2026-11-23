-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreMap_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:34.729782+00:00
-- url     : https://prove2.me/submissions/9e7bcdab-39d5-422c-ba09-4e19f5840808

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p : (k : K) → ι k) :
    segreMap (X p : MvPolynomial ((k : K) → ι k) ℂ) = ∏ k, X ⟨k, p k⟩ := by
  simp [segreMap]
end ReciprocityTheory.AnForm.R
