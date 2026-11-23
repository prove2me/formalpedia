-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_isUnit_of_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:02.179385+00:00
-- url     : https://prove2.me/submissions/90e42bb8-bbe8-4cf8-b10c-bbe92142627d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB

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
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) : IsUnit y := by
  rw [Matrix.isUnit_iff_isUnit_det]
  cases n with
  | zero => simp
  | succ m =>
    have h := hy (Fin.last m)
    simp only [lead, Fin.val_last, le_refl, dif_pos] at h
    have e : y.submatrix (Fin.castLE (le_refl (m + 1))) (Fin.castLE (le_refl (m + 1))) = y := by
      ext a b; rfl
    rw [e] at h
    exact isUnit_iff_ne_zero.mpr h
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
