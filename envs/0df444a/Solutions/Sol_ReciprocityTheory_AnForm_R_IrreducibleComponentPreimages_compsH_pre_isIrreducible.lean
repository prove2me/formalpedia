-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:36.152629+00:00
-- url     : https://prove2.me/submissions/1ab5af49-1f79-499b-95be-8f676f6b2174

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_compsH_pre_isPreirreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {α : Type*} [TopologicalSpace α]
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {T C : Set α} (hCT : C ⊆ T) (hC : IsIrreducible C) :
    IsIrreducible ((Subtype.val ⁻¹' C : Set T)) := by
  obtain ⟨c, hc⟩ := hC.nonempty
  exact ⟨⟨⟨c, hCT hc⟩, hc⟩, compsH_pre_isPreirreducible hCT hC.isPreirreducible⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
