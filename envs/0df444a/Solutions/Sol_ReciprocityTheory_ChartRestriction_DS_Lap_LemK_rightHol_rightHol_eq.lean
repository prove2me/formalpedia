-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.rightHol_rightHol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:48.54455+00:00
-- url     : https://prove2.me/submissions/9aec4134-6198-4e62-9a67-15ffcf1564a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_k2mMulRight_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Rhol X (Rhol Y F) z = fderiv ℂ F z (z * X * Y) + fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) := by
  have hd : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero
  have he : Rhol Y F = fun w => fderiv ℂ F w (matrixMulRightCLM Y w) := rfl
  show fderiv ℂ (Rhol Y F) z (z * X) = _
  have h3 := hd.hasFDerivAt.clm_apply (matrixMulRightCLM Y).hasFDerivAt
  rw [he]
  refine (congrArg (fun L => L (z * X)) h3.fderiv).trans ?_
  change fderiv ℂ F z (matrixMulRightCLM Y (z * X)) + fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = _
  rw [k2mMulRight_apply]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
