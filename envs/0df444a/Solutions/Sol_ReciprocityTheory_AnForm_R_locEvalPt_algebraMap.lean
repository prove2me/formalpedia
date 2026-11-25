-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locEvalPt_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:23.095782+00:00
-- url     : https://prove2.me/submissions/3a80af2c-9d26-4a10-af50-9eac8fdffcc5

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) (g : MvPolynomial (Fin n) ℂ) :
    locEvalPt I p hp (Ideal.Quotient.mk _ (algebraMap _ (locPt p) g)) = eval p g := by
  exact IsLocalization.lift_eq _ g
end ReciprocityTheory.AnForm.R
