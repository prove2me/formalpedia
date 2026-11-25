-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:16.516318+00:00
-- url     : https://prove2.me/submissions/9a2de9b4-72eb-4833-8d37-2abd6700dd82

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_norm_Q_le
public import Theorems.Thm_SNumbers_approximationNumber_le_norm


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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ‖S‖ :=
  (approximationNumber_le_norm _ _).trans <|
    (opNorm_comp_le _ _).trans <|
      (mul_le_mul_of_nonneg_left norm_Q_le (norm_nonneg _)).trans (mul_one _).le
end SNumbers.Lifting
