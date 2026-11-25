-- Prove2me | solution 1 for SNumbers.Lifting.Q_comp_liftA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:36.703816+00:00
-- url     : https://prove2.me/submissions/bb8e211f-5adf-4ee4-9081-d84979fd202e

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_Q_single
public import Theorems.Thm_SNumbers_Lifting_liftA_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.Lifting.liftA_apply
section
@[expose] public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
namespace SNumbers
namespace Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
section S1a
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end S1a
section S3
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
omit [CompleteSpace 𝕜] [CompleteSpace W] in
private lemma Q_liftBasis (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : (Q : BallLp 𝕜 X →L[𝕜] X) (liftBasis hc hc_ne w) = A (w : W) := by
  unfold liftBasis
  rw [Q_single _ (Aw_in_ball hc hc_ne w) c, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
end S3
section S5
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
end S5
section S5b
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
end S5b
section Pietsch
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Pietsch
end Lifting
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers.Lifting
theorem _root_.solution (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    (Q : BallLp 𝕜 X →L[𝕜] X).comp (liftA A hc hc_ne) = A.comp Q := by
  ext α
  show (Q : BallLp 𝕜 X →L[𝕜] X) (liftA A hc hc_ne α)
        = A ((Q : BallLp 𝕜 W →L[𝕜] W) α)
  rw [liftA_apply,
      (Q : BallLp 𝕜 X →L[𝕜] X).map_tsum (summable_smul_liftBasis hc hc_ne α)]
  simp_rw [map_smul, Q_liftBasis A hc hc_ne]
  rw [Q_apply, A.map_tsum (summable_smul_val α)]
  simp_rw [map_smul]
end SNumbers.Lifting
