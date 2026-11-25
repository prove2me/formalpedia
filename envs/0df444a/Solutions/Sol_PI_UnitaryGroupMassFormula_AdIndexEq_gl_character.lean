-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.gl_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:40.564663+00:00
-- url     : https://prove2.me/submissions/f64e8b23-9dbc-4831-8eb6-76def707f2f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_transvection
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_dU_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_diag
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open GLChiPf
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : GLChi := by
  intro k _ _ n χ hpos hz g
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) k)
  have htd : ∀ t : Matrix.TransvectionStruct (Fin n) k, t.toMatrix.det ≠ 0 := fun t => by
    rw [t.det]; exact one_ne_zero
  have lu_val : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (((l.map fun t => glOf t.toMatrix (htd t)).prod : Matrix.GeneralLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = (l.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]
      try rfl
  have lu_chi : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      χ ((l.map fun t => glOf t.toMatrix (htd t)).prod) = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih, chi_transvection χ hpos t (htd t), one_mul]
  have det_l : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (l.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, t.det, ih, one_mul]
  have hg0 : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hdet : (g : Matrix (Fin n) (Fin n) k).det = ∏ j, D j := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, det_l, det_l, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    rw [hdet] at hg0
    exact Finset.prod_ne_zero_iff.mp hg0 i (Finset.mem_univ i)
  have hg : g = (L.map fun t => glOf t.toMatrix (htd t)).prod * dU (fun i => Units.mk0 (D i) (hD i)) *
      (L'.map fun t => glOf t.toMatrix (htd t)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, lu_val, lu_val, dU_val]
    exact hM
  rw [hg, map_mul, map_mul, lu_chi, lu_chi, chi_diag χ hpos hz, one_mul, one_mul]
end PI.UnitaryGroupMassFormula.AdIndexEq
