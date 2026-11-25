-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:28:56.801811+00:00
-- url     : https://prove2.me/submissions/2a2cf96a-b585-44f3-af93-d622dbb948c5

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_nonneg
public import Theorems.Thm_SNumbers_Lifting_norm_liftA_le
public import Theorems.Thm_SNumbers_Lifting_Q_comp_liftA
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
public import Theorems.Thm_SNumbers_kolmogorovNumber_nonneg


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
theorem _root_.solution
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set kN := kolmogorovNumber S n
  have hkN_nn : 0 ≤ kN := kolmogorovNumber_nonneg S n
  set BkN := ‖B‖ * kN
  have hBkN_nn : 0 ≤ BkN := mul_nonneg (norm_nonneg _) hkN_nn
  have hBkN1_pos : (0 : ℝ) < BkN + 1 := by linarith
  obtain ⟨c, hc_lb, hc_ub⟩ :=
    NormedField.exists_lt_norm_lt 𝕜 (norm_nonneg A)
      (lt_add_of_pos_right ‖A‖ (div_pos hε hBkN1_pos))
  have hc_ne : c ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hc_lb)
  -- Factor: (B∘S∘A) ∘ Q_W = B ∘ ((S∘Q_X) ∘ T).
  have h_inner : (S.comp A).comp (Q : BallLp 𝕜 W →L[𝕜] W)
      = (S.comp Q).comp (liftA A hc_lb.le hc_ne) := by
    rw [ContinuousLinearMap.comp_assoc,
        show A.comp (Q : BallLp 𝕜 W →L[𝕜] W) =
             (Q : BallLp 𝕜 X →L[𝕜] X).comp (liftA A hc_lb.le hc_ne) from
          (Q_comp_liftA A hc_lb.le hc_ne).symm,
        ← ContinuousLinearMap.comp_assoc]
  show approximationNumber
      ((B.comp (S.comp A)).comp (Q : BallLp 𝕜 W →L[𝕜] W)) n ≤ ‖B‖ * kN * ‖A‖ + ε
  rw [show (B.comp (S.comp A)).comp (Q : BallLp 𝕜 W →L[𝕜] W)
        = B.comp ((S.comp Q).comp (liftA A hc_lb.le hc_ne)) by
      rw [ContinuousLinearMap.comp_assoc, h_inner]]
  refine (approximationNumber_comp_comp_le _ _ _ _).trans ?_
  -- ‖B‖ · kN · ‖T‖ ≤ ‖B‖ · kN · ‖c‖ ≤ ‖B‖ · kN · (‖A‖ + δ) ≤ ‖B‖ · kN · ‖A‖ + ε.
  calc ‖B‖ * kN * ‖liftA A hc_lb.le hc_ne‖
      ≤ ‖B‖ * kN * (‖A‖ + ε / (BkN + 1)) :=
        mul_le_mul_of_nonneg_left
          ((norm_liftA_le A hc_lb.le hc_ne).trans hc_ub.le) hBkN_nn
    _ = ‖B‖ * kN * ‖A‖ + (BkN / (BkN + 1)) * ε := by ring
    _ ≤ ‖B‖ * kN * ‖A‖ + 1 * ε := by
        gcongr; exact (div_le_one hBkN1_pos).mpr (by linarith)
    _ = ‖B‖ * kN * ‖A‖ + ε := by ring
end SNumbers.Lifting
