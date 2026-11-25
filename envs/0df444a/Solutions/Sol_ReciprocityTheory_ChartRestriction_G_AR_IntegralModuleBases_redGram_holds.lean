-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:00.285195+00:00
-- url     : https://prove2.me/submissions/f7a827eb-f915-4280-8678-f3762ad8810c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_fB_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_det_gram_fB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_red_coeff_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_red_norm_sq_le
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_exists_red_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_expand
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_hlow_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_li_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution : RedGramStatement := by
  intro d A m D hA hm hmin hD
  obtain ⟨B, hAB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᴴ * B := by
    refine ⟨CFC.sqrt A, ?_⟩
    have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
    have hsa : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    rw [← Matrix.star_eq_conjTranspose, hsa.star_eq, CFC.sqrt_mul_sqrt_self A h0]
  obtain ⟨e, hre⟩ := exists_red_of (fB B) (fun e => (li_basis A B hA hAB e).2) (hlow_of A B hA hAB)
  have hm' : ∀ i, m ≤ ‖fB B (e i)‖ ^ 2 := by
    intro i
    rw [norm_fB_sq A B hAB]
    exact hmin _ (e.ne_zero i)
  refine ⟨e, fun i => ?_, fun x i => ?_⟩
  · have h1 := red_norm_sq_le _ hre m D hm hm' (by rw [det_gram_fB A B hAB e]; exact hD) i
    rw [norm_fB_sq A B hAB] at h1
    exact h1
  · have h1 := red_coeff_sq_le _ hre m hm hm' (fun l => ((e.repr x l : ℤ) : ℝ)) i
    rw [← fB_expand B e x, norm_fB_sq A B hAB] at h1
    exact h1
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
