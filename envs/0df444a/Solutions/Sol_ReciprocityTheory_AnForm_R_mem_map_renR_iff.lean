-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mem_map_renR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:38.358975+00:00
-- url     : https://prove2.me/submissions/3ea8f071-7edd-4d28-a5b6-cc1833283117

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer

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
noncomputable section
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial (Fin (Fintype.card σ)) ℂ) :
    h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _) ↔ (renR σ).symm h ∈ I := by
  rw [Ideal.map_comap_of_equiv]
  exact Iff.rfl
end ReciprocityTheory.AnForm.R
