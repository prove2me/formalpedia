-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lhol_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:38.989366+00:00
-- url     : https://prove2.me/submissions/b3fb63c3-e235-4089-bd23-2badfda69ace

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_lhol_eq

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = Lhol Y (Lhol X F) z + fderiv ℂ F z ((Y * X - X * Y) * z) := by
  rw [lhol_lhol_eq hF, lhol_lhol_eq hF]
  have hs := hF.isSymmSndFDerivAt (by simp)
  have h1 : fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) :=
    hs _ _
  have h2 : fderiv ℂ F z ((Y * X - X * Y) * z) =
      fderiv ℂ F z (Y * (X * z)) - fderiv ℂ F z (X * (Y * z)) := by
    rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  linear_combination -h1 - h2
end ReciprocityTheory.ChartRestriction.DS.S7
