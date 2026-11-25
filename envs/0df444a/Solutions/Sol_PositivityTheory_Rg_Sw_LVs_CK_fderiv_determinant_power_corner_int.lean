-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.fderiv_determinant_power_corner_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:08.178799+00:00
-- url     : https://prove2.me/submissions/adae1105-2cbc-4e21-b295-88cc0f1b525c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_fderiv_line
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_phiF
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_H
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_first_row_expansion
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply



set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) = (t : ℂ) * H N t (piF X) := by
  set d := (1 + piF X).det with hd
  have hdiff : DifferentiableAt ℂ (H (N + 1) t) (phiF X) :=
    (analyticAt_H (N + 1) t (phiF X) (by rw [det_phiF]; exact hX)).differentiableAt
  have hl := fderiv_line (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) hdiff
  have heq : (fun s : ℂ => H (N + 1) t (phiF X + s • Matrix.single 0 0 1)) =
      fun s => ((1 + s) * d) ^ t := by
    funext s
    simp only [H]
    congr 1
    have h0 : ∀ j : Fin (N + 1),
        ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) + (phiF X + s •
          (Matrix.single 0 0 1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))) 0 j =
        if j = 0 then 1 + s else 0 := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [phiF_zero_row]
      · simp [phiF_zero_row, Matrix.one_apply, (Fin.succ_ne_zero j).symm, Matrix.single_apply]
    rw [det_first_row_expansion _ (1 + s) h0]
    congr 2
    ext k l
    simp [Matrix.one_apply, phiF_succ_row, piF, Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  rw [heq] at hl
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_add 1).mul_const d
  have hz := (hasDerivAt_zpow t ((1 + 0) * d) (Or.inl (by simpa using hX))).comp (0:ℂ) hf
  refine (hl.unique hz).trans ?_
  simp only [H, ← hd, add_zero, one_mul]
  rw [zpow_sub_one₀ hX]
  field_simp
end PositivityTheory.Rg.Sw.LVs.CK
