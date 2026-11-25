-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_sUnion_compsH_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:46.688678+00:00
-- url     : https://prove2.me/submissions/7e0f02a0-a17a-41a1-87cf-76644e778630

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_compsH_finite
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_of_mem_compsH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution [IsNoetherian W] {T : Set W} (hT : IsClosed T) (y : W) :
    IsClosed (⋃₀ {D | D ∈ compsH T ∧ y ∉ D}) := by
  rw [Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion ((compsH_finite T).subset fun D hD => hD.1)
    fun D hD => isClosed_of_mem_compsH hT hD.1
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
