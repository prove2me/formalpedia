-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.qe_projX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:54.885158+00:00
-- url     : https://prove2.me/submissions/9c71213d-1f22-4143-b37d-42f2ac543486

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartOpen_cover
import Theorems.Thm_ReciprocityTheory_AnForm_R_qeRing_gammaChart


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
    (hQE : FinalTheorems.FinTypeQE) : FinalTheorems.QE (projX P hP) := by
  intro x
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact ⟨chartOpen hP p, hp, qeRing_gammaChart hP hQE p⟩
end ReciprocityTheory.AnForm.R
