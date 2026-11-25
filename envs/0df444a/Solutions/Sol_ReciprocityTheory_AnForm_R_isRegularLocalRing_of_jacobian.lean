-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isRegularLocalRing_of_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:45.452986+00:00
-- url     : https://prove2.me/submissions/e579a8ba-bd4f-44f9-bd1b-57c47536c66a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isRegularLocalRing_of_jacobian__1669e12dca9e


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
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => grad p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locRing K p) ∧ ringKrullDim (locRing K p) = ((n - c : ℕ) : WithBot ℕ∞) := by
  exact JacobianCriterionAlt.isRegularLocalRing_of_jacobian' K p hp F hF hlin hq
end ReciprocityTheory.AnForm.R
