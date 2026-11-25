-- Prove2me | solution 1 for SNumbers.L1Linf.norm_e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:39.313868+00:00
-- url     : https://prove2.me/submissions/f720569b-e1b2-4718-a7c8-2ac117915ce9

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (i : ℕ) : ‖(e i : L1 𝕜)‖ = 1 := by
  unfold e; rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one]
end SNumbers.L1Linf
