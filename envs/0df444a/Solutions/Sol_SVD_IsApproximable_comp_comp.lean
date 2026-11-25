-- Prove2me | solution 1 for SVD.IsApproximable.comp_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:43.766272+00:00
-- url     : https://prove2.me/submissions/fa7232f3-2461-480b-ac7d-d5d42febcef0

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SVD
namespace IsApproximable
theorem _root_.solution {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (B : Y →L[𝕜] Z) (hS : IsApproximable S) :
    IsApproximable (B.comp (S.comp A)) := by
  -- Bound: aₙ(BSA) ≤ ‖B‖ · aₙ(S) · ‖A‖, then squeeze.
  have h_bd : ∀ n, SNumbers.approximationNumber (B.comp (S.comp A)) n ≤
                    ‖B‖ * SNumbers.approximationNumber S n * ‖A‖ :=
    fun n => SNumbers.approximationNumber_comp_comp_le A S B n
  have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber (B.comp (S.comp A)) n :=
    fun n => SNumbers.approximationNumber_nonneg _ n
  have h_lim :
      Tendsto (fun n => ‖B‖ * SNumbers.approximationNumber S n * ‖A‖)
        atTop (𝓝 0) := by
    have h1 := (hS.const_mul ‖B‖).mul_const ‖A‖
    simpa using h1
  exact squeeze_zero h_nonneg h_bd h_lim
end IsApproximable
end SVD
