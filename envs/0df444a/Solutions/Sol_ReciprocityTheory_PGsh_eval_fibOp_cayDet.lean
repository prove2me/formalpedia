-- Prove2me | solution 1 for ReciprocityTheory.PGsh.eval_fibOp_cayDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:19:33.024908+00:00
-- url     : https://prove2.me/submissions/7105dca3-b487-485c-9f6f-e352e7323b70

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_prod_map_ite_one
import Theorems.Thm_ReciprocityTheory_PGsh_list_pderiv_yP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (σ : Fin n → Fin n) {s : ℕ} (φ : Fin n → Fin s) (k : Fin s) :
    eval onePt (fibOp σ φ k (cayDet n ℤ)) =
      (funMat fun b => if φ b = k then σ b else b).det := by
  have hf : fibOp σ φ k = (((List.finRange n).filter fun j => φ j = k).map fun j =>
      ((pderiv (σ j, j) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ) _) :
        MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod := by
    unfold fibOp
    rw [List.ofFn_eq_map, prod_map_ite_one]
  have hc : cayDet n ℤ = ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • yP σ τ ∅ := by
    simp [cayDet, Matrix.det_apply, yP, Units.smul_def, Matrix.mvPolynomialX_apply]
  have hS : ((List.finRange n).filter fun j => φ j = k).toFinset =
      Finset.univ.filter fun b => φ b = k := by
    ext b; simp
  rw [hf, hc, map_sum, map_sum, Matrix.det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_zsmul, list_pderiv_yP σ τ _ (List.Nodup.filter _ (List.nodup_finRange n)) ∅ (by simp),
    Finset.empty_union, hS, map_zsmul, Units.smul_def]
  congr 1
  simp only [yP, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : φ b = k
  · simp [hb, funMat, onePt, apply_ite (eval onePt)]
  · simp [hb, funMat, onePt, Matrix.one_apply, apply_ite (eval onePt)]
end ReciprocityTheory.PGsh
