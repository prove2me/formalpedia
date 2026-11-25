-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:28:55.72746+00:00
-- url     : https://prove2.me/submissions/a64edce1-12e2-47d8-a55c-5601a42708af

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_norm_Q_le
public import Theorems.Thm_SNumbers_approximationNumber_add_le


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
namespace SNumbers.Lifting
theorem _root_.solution (S T : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S + T) n ≤ kolmogorovNumber S n + ‖T‖ := by
  unfold kolmogorovNumber
  rw [ContinuousLinearMap.add_comp]
  have h_TQ : ‖T.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ ≤ ‖T‖ :=
    (opNorm_comp_le _ _).trans <|
      (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le
  linarith [approximationNumber_add_le (S.comp Q) (T.comp Q) n]
end SNumbers.Lifting
