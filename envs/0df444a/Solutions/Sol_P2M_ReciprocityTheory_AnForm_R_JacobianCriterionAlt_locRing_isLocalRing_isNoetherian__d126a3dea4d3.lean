-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:25.825847+00:00
-- url     : https://prove2.me/submissions/ad8497eb-6e26-4c93-85da-bf1b72c3044e

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isNoetherianRing_locPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locR K p) ∧ IsNoetherianRing (locR K p) := by
  haveI := isNoetherianRing_locPt p
  have hK : K ≤ ptI p := fun h hh => by rw [ptI, RingHom.mem_ker]; exact hp h hh
  have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K ≤ IsLocalRing.maximalIdeal (localization₂ p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hK
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K ≠ ⊤ :=
    fun h => (IsLocalRing.maximalIdeal.isMaximal (localization₂ p)).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (locR K p) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, inferInstance⟩
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
