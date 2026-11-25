-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InhabA.hasDerivAt_blockDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:52.983242+00:00
-- url     : https://prove2.me/submissions/d42369ce-7945-4d7c-92e2-438ffb819f83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_exp_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_det_of_one

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
theorem _root_.solution (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) :
    HasDerivAt (fun t : ℝ => ((NormedSpace.exp ((t : ℂ) • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det)
      (∑ a ∈ univ.filter (fun a => ε a = s), X a a) 0 := by
  have h := hasDerivAt_det_of_one
    (fun t : ℝ => (NormedSpace.exp (t • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (by simp [NormedSpace.exp_zero, Matrix.submatrix_one _ Subtype.val_injective])
    (fun i j => hasDerivAt_exp_entry X i.1 j.1)
  have ht : (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).trace =
      ∑ a ∈ univ.filter (fun a => ε a = s), X a a := by
    rw [Matrix.trace]
    exact (Finset.sum_subtype _ (fun l => by simp) (fun l => X l l)).symm
  rw [ht] at h
  simpa only [Complex.coe_smul] using h
end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
