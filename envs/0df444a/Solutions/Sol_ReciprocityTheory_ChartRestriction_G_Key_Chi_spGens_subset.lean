-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spGens_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:32.931924+00:00
-- url     : https://prove2.me/submissions/aebc388e-edd6-4861-9c03-f6955806c231

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem_sp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem_sp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (g : ℕ) : spGens g ⊆ symplecticGroup (Fin g) ℤ := by

  intro x hx
  rcases hx with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ
  · exact spTransl_mem_sp hS
  · exact spDiag_mem_sp U
  · rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact SymplecticGroup.J_mem _ _
end ReciprocityTheory.ChartRestriction.G.Key.Chi
