-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.projectiveLineLift_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:24:09.793977+00:00
-- url     : https://prove2.me/submissions/b5fe38e5-d0d3-44ee-9376-70f8923af4f9

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineHomogeneousLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (q : Σ _ : Unit, Fin 2) : homogeneousLift 0 q = if q.2 = 0 then 1 else X 0 := rfl
end ReciprocityTheory.AnForm.R
