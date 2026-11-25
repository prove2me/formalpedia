-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:31.390045+00:00
-- url     : https://prove2.me/submissions/219bf094-5d50-482a-b013-62295f684acc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply


attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.GaussGen
theorem _root_.solution {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → K) (t : TVar D N) :
    translS j₀ (fun j => algebraMap K Ω (a j)) (Pimg j₀ x t) =
      aeval (Pimg j₀ x) (transl a (X t)) := by
  obtain ⟨i, j⟩ := t
  rw [transl_X]
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩ <;> by_cases hi : i = 0
  · subst hi
    simp [Pimg_self, translS, blk, col, MvPolynomial.algebraMap_apply]
  · simp [Pimg_self, translS, blk, col, hi, map_sum, map_neg]
  · subst hi
    simp [Pimg_succAbove, translS, blk, col, MvPolynomial.algebraMap_apply]
  · simp [Pimg_succAbove, translS, blk, col, hi]
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
