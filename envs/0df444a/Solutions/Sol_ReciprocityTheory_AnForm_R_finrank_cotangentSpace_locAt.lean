-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:38.924068+00:00
-- url     : https://prove2.me/submissions/00754022-4eb3-41e0-a301-f5e4ca096f27

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_jacSpanAt_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_eq_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_cotangentSpace_locRing


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
theorem _root_.solution {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (z : σ → ℂ) [IsLocalRing (locAt I z)] :
    Module.finrank (ResidueField (locAt I z)) (CotangentSpace (locAt I z))
      + Module.finrank ℂ (jacSpanAt I z) = Fintype.card σ := by
  haveI : IsNoetherianRing (locAt I z) := inferInstance
  haveI : Nontrivial (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    (locAtEquiv I z).symm.toEquiv.nontrivial
  haveI : IsLocalRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    IsLocalRing.of_surjective' (locAtEquiv I z).toRingHom (locAtEquiv I z).surjective
  haveI : IsNoetherianRing (locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) :=
    isNoetherianRing_of_ringEquiv _ (locAtEquiv I z)
  rw [finrank_cotangentSpace_eq_of_ringEquiv (locAtEquiv I z), finrank_jacSpanAt_eq,
    finrank_cotangentSpace_locRing]
end ReciprocityTheory.AnForm.R
