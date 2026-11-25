-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.chiP_rename_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:48:07.118472+00:00
-- url     : https://prove2.me/submissions/c9cdec9d-638e-402a-91ec-25d54814b6d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
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
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K) :
    chiP (K := K) j₀ x (rename swapT g) = rename swapS (chiP (K := K) j₀ x g) := by
  have key : ∀ p : TVar D N, chiImg j₀ x (swapT p) = rename swapS (chiImg j₀ x p) := by
    rintro ⟨b, j⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same, map_sum, map_neg]
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  induction g using MvPolynomial.induction_on with
  | C a => simp [chiP]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    simp only [chiP, aeval_X, key]
end ReciprocityTheory.ChartRestriction.G.T0
