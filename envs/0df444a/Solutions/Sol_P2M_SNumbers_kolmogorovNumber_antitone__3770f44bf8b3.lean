-- Prove2me | solution 1 for P2M_SNumbers_kolmogorovNumber_antitone__3770f44bf8b3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:09.004508+00:00
-- url     : https://prove2.me/submissions/9a5e86d6-2a6d-4899-9953-c8d4defec7d0

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovSet_nonempty
public import Theorems.Thm_SNumbers_bddBelow_kolmogorovSet
public import Theorems.Thm_SNumbers_kolmogorovSet_subset

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovNumber S m ≤ kolmogorovNumber S n :=
  csInf_le_csInf (bddBelow_kolmogorovSet S m) (kolmogorovSet_nonempty S n)
    (kolmogorovSet_subset S h)
end SNumbers
