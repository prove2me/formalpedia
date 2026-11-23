-- Prove2me | solution 1 for P2M_GlobalTheory_PsiQuadratic___self_27515abbac20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:53.882721+00:00
-- url     : https://prove2.me/submissions/4b0254b8-144d-424c-a3c7-3eae80d8493e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
import Theorems.Thm_P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.PsiQuadratic
theorem _root_.solution (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by
  have a := N.τ_add_left y (-y) y
  rw [add_neg_cancel, N.τ_zero_left, one_mul, N.c_neg] at a
  have b := N.ψ_add (-y) y
  rw [neg_add_cancel, N.ψ_zero] at b
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul (N.even y)
  apply Additive.ofMul.injective
  simp only [dbl, sq, ofMul_mul, ofMul_div, ofMul_one] at a' b' c' ⊢
  linear_combination (norm := abel) -a' + b' + c'
end GlobalTheory.PsiQuadratic
