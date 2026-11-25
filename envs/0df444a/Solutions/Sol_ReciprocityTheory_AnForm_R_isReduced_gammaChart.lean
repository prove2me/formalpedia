-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isReduced_gammaChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:05.241967+00:00
-- url     : https://prove2.me/submissions/e57afa17-20d3-4673-b472-e6a811c02807

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Theorems.Thm_ReciprocityTheory_AnForm_R_isReduced_away

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
    (hrad : P.IsRadical) (p : (k : K) → ι k) :
    _root_.IsReduced Γ(projX P hP, (chartOpen hP p).1) := by
  letI := segreGraded hP
  have := isReduced_away hP hrad p
  exact isReduced_of_injective _ ((gammaChart hP p).trans (awayEquiv hP p)).injective
end ReciprocityTheory.AnForm.R
