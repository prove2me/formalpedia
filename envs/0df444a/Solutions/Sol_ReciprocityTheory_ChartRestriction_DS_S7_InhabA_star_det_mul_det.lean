-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InhabA.star_det_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:46.662798+00:00
-- url     : https://prove2.me/submissions/6543bc18-fc8c-4b67-9f39-24edf89929eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_eq_zero_of_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_submatrix_mul_blk

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.InhabA
open ReciprocityTheory.ChartRestriction.DS
variable {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InhabA
theorem _root_.solution {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    star (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det *
      (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det = 1 := by
  have hb := eq_zero_of_comm hk.2
  have hbs : ∀ i j, ε i ≠ ε j → kᴴ i j = 0 := fun i j hij => by
    rw [Matrix.conjTranspose_apply, hb j i (Ne.symm hij), star_zero]
  have hu : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, Matrix.conjTranspose_submatrix,
    ← submatrix_mul_blk s hbs k, hu, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
