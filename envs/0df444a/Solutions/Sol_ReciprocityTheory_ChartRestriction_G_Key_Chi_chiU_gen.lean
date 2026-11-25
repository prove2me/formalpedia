-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:04.733101+00:00
-- url     : https://prove2.me/submissions/66d92309-a98a-4eff-af95-923fb365f00d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_spDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_J

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} (hInv : InversionStatement) {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ spGens g) : ChiAtU g γ := by
  simp only [spGens, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hγ
  rcases hγ with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | rfl
  · exact chiU_spTransl S hS
  · exact chiU_spDiag U
  · exact chiU_J hInv
end ReciprocityTheory.ChartRestriction.G.Key.Chi
