-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:54.969434+00:00
-- url     : https://prove2.me/submissions/84c51a09-7d2d-4607-9a8a-a18a438c534f

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_norm_Q_le
public import Theorems.Thm_SNumbers_Lifting_norm_le_norm_comp_Q
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



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
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Lifting
theorem _root_.solution (S : X →L[𝕜] Y) :
    kolmogorovNumber S 0 = ‖S‖ := by
  unfold kolmogorovNumber
  rw [approximationNumber_zero_eq_norm]
  refine le_antisymm ?_ (norm_le_norm_comp_Q S)
  refine (opNorm_comp_le _ _).trans ?_
  exact (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le
end SNumbers.Lifting
