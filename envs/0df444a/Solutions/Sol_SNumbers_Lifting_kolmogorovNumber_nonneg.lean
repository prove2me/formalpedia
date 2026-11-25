-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:03.468615+00:00
-- url     : https://prove2.me/submissions/135d74dc-d356-464e-bd4e-50515af885fe

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_approximationNumber_nonneg


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
    0 ≤ kolmogorovNumber S n :=
  approximationNumber_nonneg _ _
end SNumbers.Lifting
