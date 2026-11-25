-- Prove2me | solution 1 for PI.RhsWLim.W.DL_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:47.197182+00:00
-- url     : https://prove2.me/submissions/c93da6f4-8787-4697-9d15-75d33cb4efaf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_DL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.RhsWLim.W.DL_apply

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) (hT : 0 < T') : (DL k T').det = (T' / 2) ^ k := by
  show LinearMap.det (DL k T' : TrE k →ₗ[ℝ] TrE k) = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis]
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis
      (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis (DL k T' : TrE k →ₗ[ℝ] TrE k)
      = Matrix.diagonal (dgn T') := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, DL_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hm, Matrix.det_diagonal, Fintype.prod_option]
  simp only [dgn, one_mul]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    mul_comm k 2, pow_mul, div_pow, Real.sq_sqrt hT.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
end PI.RhsWLim.W
