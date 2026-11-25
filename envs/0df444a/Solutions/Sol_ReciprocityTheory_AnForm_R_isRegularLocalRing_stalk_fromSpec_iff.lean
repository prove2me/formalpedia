-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isRegularLocalRing_stalk_fromSpec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:58.235369+00:00
-- url     : https://prove2.me/submissions/fd7313ef-aaaf-402c-bc0f-430a7b4e0c1a

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) ↔
      IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
    (X.presheaf.stalk (hU.fromSpec y))
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun h => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩
end ReciprocityTheory.AnForm.R
