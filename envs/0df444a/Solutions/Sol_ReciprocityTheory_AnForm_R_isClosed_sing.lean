-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isClosed_sing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:56:11.722092+00:00
-- url     : https://prove2.me/submissions/1e8ba63a-df0c-4150-9491-744d1393f661

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartOpen_cover
import Theorems.Thm_ReciprocityTheory_AnForm_R_isOpen_regularLocus_of_cover
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
    (hQE : FinalTheorems.FinTypeQE) : IsClosed (FinalTheorems.Sing (projX P hP)) := by
  have hopen := isOpen_regularLocus_of_cover (fun p => chartOpen hP p) (chartOpen_cover hP)
    (fun p => (qeRing_gammaChart hP hQE p).2.2 _)
  exact hopen.isClosed_compl
end ReciprocityTheory.AnForm.R
