-- Prove2me | solution 1 for P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:36.131318+00:00
-- url     : https://prove2.me/submissions/fa37db41-a41f-4a65-993f-6e491cd87336

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RingKrullDimLocRingEqOfMinimalPrime

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)
end ReciprocityTheory.AnForm.R
