-- Prove2me | solution 1 for PI.WMI.lowerInv_torus_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:53.824082+00:00
-- url     : https://prove2.me/submissions/1d068eff-2bdf-4e14-ab21-2daf0910ac52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (θ : Fin N → ℝ) : torus θ ∈ Kset (allPos N) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, torus, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  · simp [Jm, allPos]
end PI.WMI
