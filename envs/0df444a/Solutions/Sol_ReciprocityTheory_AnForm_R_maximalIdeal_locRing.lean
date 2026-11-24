-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.maximalIdeal_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:16.574501+00:00
-- url     : https://prove2.me/submissions/8b51415d-936b-4c80-a212-811d6a1e6a9a

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
    (hK : K ≤ ptIdeal p) [IsLocalRing (locRing K p)] :
    IsLocalRing.maximalIdeal (locRing K p) = (ptIdeal p).map (algebraMap _ (locRing K p)) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (ptQ K p) (locRing K p), ptQ, Ideal.map_map]
  congr 1
end ReciprocityTheory.AnForm.R
