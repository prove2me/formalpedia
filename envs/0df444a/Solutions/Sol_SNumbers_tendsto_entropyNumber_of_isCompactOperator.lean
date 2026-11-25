-- Prove2me | solution 1 for SNumbers.tendsto_entropyNumber_of_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:54:48.277051+00:00
-- url     : https://prove2.me/submissions/a0874533-f868-41ec-9b38-8b3e43f0f6e7

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_iff_totallyBounded

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    Tendsto (entropyNumber S) atTop (𝓝 0) := by
  have hS' : IsCompactOperator ⇑(S : X →ₗ[𝕜] Y) := hS
  have h_cpt := hS'.isCompact_closure_image_closedBall (1 : ℝ)
  rw [ContinuousLinearMap.coe_coe] at h_cpt
  exact (tendsto_entropyNumber_iff_totallyBounded S).mpr
    (TotallyBounded.subset subset_closure h_cpt.totallyBounded)
end SNumbers
