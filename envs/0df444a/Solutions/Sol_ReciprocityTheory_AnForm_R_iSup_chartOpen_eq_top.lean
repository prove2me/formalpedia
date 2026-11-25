-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.iSup_chartOpen_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:23:56.280357+00:00
-- url     : https://prove2.me/submissions/8d7b94ff-c5fd-4d50-ab4c-5d58fa73d8a1

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartOpen_cover


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
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    (⨆ p : (k : K) → ι k, ((chartOpen hP p).1 : (projX P hP).Opens)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, hp⟩ := chartOpen_cover hP x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hp⟩
end ReciprocityTheory.AnForm.R
