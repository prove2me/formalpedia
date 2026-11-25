-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.rightHol_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:06.066632+00:00
-- url     : https://prove2.me/submissions/b5e3cc6e-ee1e-4569-966d-bd314a3afc97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_rightHol_rightHol_eq

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
    Rhol X (Rhol Y F) z - Rhol Y (Rhol X F) z = Rhol (X * Y - Y * X) F z := by
  have hs : IsSymmSndFDerivAt ℂ F z := hF.isSymmSndFDerivAt
    (by first | simp [minSmoothness_of_isRCLikeNormedField] | simp | exact le_rfl)
  have h2 : fderiv ℂ (fderiv ℂ F) z (z * X) (z * Y) = fderiv ℂ (fderiv ℂ F) z (z * Y) (z * X) :=
    hs _ _
  rw [rightHol_rightHol_eq hF, rightHol_rightHol_eq hF, h2]
  simp only [Rhol]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
  ring
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
