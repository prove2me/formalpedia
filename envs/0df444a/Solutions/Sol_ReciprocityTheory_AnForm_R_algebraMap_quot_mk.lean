-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.algebraMap_quot_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:44.346986+00:00
-- url     : https://prove2.me/submissions/e21fb313-8ad0-4db1-abfe-d124b197edb2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ ⧸ K) (locRing K p) (Ideal.Quotient.mk K f) =
      algebraMap _ (locRing K p) f := by
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
end ReciprocityTheory.AnForm.R
