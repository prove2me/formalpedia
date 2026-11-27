-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.projectiveLineCoord_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:34:51.389698+00:00
-- url     : https://prove2.me/submissions/5883e054-abaa-4ea3-8ec7-ef35a5d8733a

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
theorem _root_.solution (x : OnePoint ℂ) : projLineAffineCoordinate 1 x = fun _ => x.elim 0 (fun z => z⁻¹) := by
  funext l
  simp [projLineAffineCoordinate]
end ReciprocityTheory.AnForm.R
