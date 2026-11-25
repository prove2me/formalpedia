-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isReduced_projX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:49:54.515602+00:00
-- url     : https://prove2.me/submissions/807816c2-947d-48cb-bed0-3ac5884c9939

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartOpen_cover
import Theorems.Thm_ReciprocityTheory_AnForm_R_isReduced_gammaChart


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
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hrad : P.IsRadical) : IsReduced (projX P hP) := by
  haveI : ∀ x : projX P hP, _root_.IsReduced ((projX P hP).presheaf.stalk x) := by
    intro x
    obtain ⟨p, hp⟩ := chartOpen_cover hP x
    have hU := (chartOpen hP p).2
    let x' : ((chartOpen hP p).1 : Set (projX P hP)) := ⟨x, hp⟩
    show _root_.IsReduced ((projX P hP).presheaf.stalk (x' : projX P hP))
    letI := TopCat.Presheaf.algebra_section_stalk (projX P hP).presheaf x'
    haveI := hU.isLocalization_stalk x'
    exact isReduced_localizationPreserves (hU.primeIdealOf x').asIdeal.primeCompl _
      (isReduced_gammaChart hP hrad p)
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _
end ReciprocityTheory.AnForm.R
