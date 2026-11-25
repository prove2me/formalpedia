-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locAt_isLocalRing_isNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:18.68284+00:00
-- url     : https://prove2.me/submissions/a5d1090e-14ef-41ed-afc9-716be506e0cc

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    IsLocalRing (locAt I z) ∧ IsNoetherianRing (locAt I z) := by
  haveI := Fintype.ofFinite σ
  have hle : I ≤ ptIdealOf z := fun h hh => by
    show h ∈ RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)
    exact hz h hh
  have hne : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I ≠ ⊤ := by
    intro htop
    have h1 : Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)))
        (ptIdealOf z) = ⊤ := top_unique (htop ▸ Ideal.map_mono hle)
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  haveI : Nontrivial (locAt I z) := Ideal.Quotient.nontrivial_iff.2 hne
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, inferInstance⟩
end ReciprocityTheory.AnForm.R
