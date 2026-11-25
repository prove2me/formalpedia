-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_eq_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:20.258779+00:00
-- url     : https://prove2.me/submissions/e0603973-cc8a-4871-8688-d27b95d921c5

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_le_approx
public import Theorems.Thm_SNumbers_Lifting_approx_le_kolmogorovNumber

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
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Lifting
namespace _root_.SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    SNumbers.kolmogorovNumber S n
      = approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n :=
  le_antisymm (kolmogorovNumber_le_approx S n) (approx_le_kolmogorovNumber S n)
end _root_.SNumbers
end SNumbers.Lifting
