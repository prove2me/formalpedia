-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.eval_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:08.161378+00:00
-- url     : https://prove2.me/submissions/80fe637e-51c3-45a2-8379-537747ebd63e

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ)
    (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval y (psi sg tt q) = eval₂ sg (gpt tt y) q := by
  have : (eval y).comp (psi sg tt) = eval₂Hom sg (gpt tt y) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [psi, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [psi, homog]
      | succ i => simp [psi, homog]
  exact congrArg (fun f => f q) this
end ReciprocityTheory.ChartRestriction.G.T0.NPB
