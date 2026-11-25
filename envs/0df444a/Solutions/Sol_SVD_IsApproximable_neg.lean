-- Prove2me | solution 1 for SVD.IsApproximable.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:36.306706+00:00
-- url     : https://prove2.me/submissions/257a6899-3387-4aaa-b591-95f5d0cabd14

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_IsApproximable_smul

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
theorem _root_.solution {S : X →L[𝕜] Y} (hS : IsApproximable S) :
    IsApproximable (-S) := by
  have h := hS.smul (-1 : 𝕜)
  rwa [neg_one_smul] at h
end IsApproximable
end SVD
