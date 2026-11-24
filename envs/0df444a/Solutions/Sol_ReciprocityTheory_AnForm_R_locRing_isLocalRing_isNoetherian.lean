-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locRing_isLocalRing_isNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:53.343814+00:00
-- url     : https://prove2.me/submissions/ee914373-180b-4600-8ec5-863dc543319f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart

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
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locRing K p) ∧ IsNoetherianRing (locRing K p) := by
  have hK : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤
      IsLocalRing.maximalIdeal (locPt p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    have h2 : h ∈ ptIdeal p := (RingHom.mem_ker).2 (hp h hh)
    rw [← Localization.AtPrime.comap_maximalIdeal (I := ptIdeal p)] at h2
    exact h2
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hK
  haveI : Nontrivial (locRing K p) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsNoetherianRing (locPt p) :=
    IsLocalization.isNoetherianRing (ptIdeal p).primeCompl _ inferInstance
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
    inferInstance⟩
end ReciprocityTheory.AnForm.R
