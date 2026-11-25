-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isLocalRing_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:19.343153+00:00
-- url     : https://prove2.me/submissions/630e40b3-985b-41eb-95a0-74a2227b1506

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Theorems.Thm_ReciprocityTheory_AnForm_R_isLocalization_locRing

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
theorem _root_.solution {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) : IsLocalRing (locRing K p) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  exact IsLocalization.AtPrime.isLocalRing (locRing K p) (ptQ K p)
end ReciprocityTheory.AnForm.R
