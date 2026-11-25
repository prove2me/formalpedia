-- Prove2me | solution 1 for SNumbers.L1Linf.e_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:35.48577+00:00
-- url     : https://prove2.me/submissions/54d25212-eb1e-4833-acd2-a98c6a20c8fb

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
theorem _root_.solution {i j : ℕ} (h : j ≠ i) : (e i : L1 𝕜) j = 0 :=
  lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 1 i (1 : 𝕜) h
end SNumbers.L1Linf
