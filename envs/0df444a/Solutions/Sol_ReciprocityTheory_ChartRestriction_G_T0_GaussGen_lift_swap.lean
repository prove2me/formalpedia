-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:35:16.830614+00:00
-- url     : https://prove2.me/submissions/cd699a71-d5ca-4069-ad01-4dd1e5111da3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_succAbove
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.GaussGen
theorem _root_.solution {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (e : Equiv.Perm (Fin (D + 1))) (he : e 0 = 0) (t : TVar D N) :
    rename (eS e) (Pimg j₀ x t) = aeval (Pimg j₀ x) (rename (eT e) (X t) : MvPolynomial _ K) := by
  obtain ⟨i, j⟩ := t
  rw [rename_X, aeval_X]
  show rename (eS e) (Pimg j₀ x (i, j)) = Pimg j₀ x (e i, j)
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
  · rw [Pimg_self, Pimg_self]
    by_cases hi : i = 0
    · subst hi
      simp [he, eS]
    · have hei : e i ≠ 0 := fun h' => hi (e.injective (h'.trans he.symm))
      simp [hi, hei, eS, map_sum, map_neg]
  · rw [Pimg_succAbove, Pimg_succAbove, rename_X]
    rfl
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
