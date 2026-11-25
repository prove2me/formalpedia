-- Prove2me | solution 1 for P2M_SNumbers_entropyNumber_antitone__7948be0d85af
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:51.522929+00:00
-- url     : https://prove2.me/submissions/eba8c30a-a3d6-4d22-bcf2-5047f97faf00

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropySet_nonempty
public import Theorems.Thm_SNumbers_bddBelow_entropySet
public import Theorems.Thm_SNumbers_entropySet_subset

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
theorem _root_.solution (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropyNumber S m ≤ entropyNumber S n :=
  csInf_le_csInf (bddBelow_entropySet S m) (entropySet_nonempty S n)
    (entropySet_subset S h)
end SNumbers
