-- Prove2me | solution 1 for SNumbers.Lifting.norm_liftA_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:33.309509+00:00
-- url     : https://prove2.me/submissions/63743b38-4621-4493-b133-3415460749f4

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting

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
omit [CompleteSpace W] [CompleteSpace X]
namespace SNumbers.Lifting
theorem _root_.solution (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    ‖liftA A hc hc_ne‖ ≤ ‖c‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
end SNumbers.Lifting
