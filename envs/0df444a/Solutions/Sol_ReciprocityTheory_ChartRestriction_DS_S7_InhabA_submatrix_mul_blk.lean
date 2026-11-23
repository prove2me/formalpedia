-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InhabA.submatrix_mul_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:58.004689+00:00
-- url     : https://prove2.me/submissions/04a0e722-68c1-4103-bc89-968fc5e4bdf3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA

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
theorem _root_.solution {ε : Fin m → Bool} (s : Bool) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : ∀ i j, ε i ≠ ε j → g i j = 0) (h : Matrix (Fin m) (Fin m) ℂ) :
    (g * h).submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) =
      g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) *
        h.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := fun l => ε l = s)]
  · exact Finset.sum_subtype _ (fun l => by simp) (fun l => g x.1 l * h l y.1)
  · intro l _ hl
    by_contra hne
    exact hl (by rw [hg x.1 l (by rw [x.2]; exact Ne.symm hne), zero_mul])
end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
