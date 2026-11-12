-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_family_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:24:20.440598+00:00
-- url     : https://prove2.me/submissions/4fb7c723-7e48-484c-b192-d9d482a94b19

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_family_mass_le_exp

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    pZ S n β (zFamily S n W) ≤ ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.family_mass_le_exp (xSyndrome S n) (2*β) W
end QEC.Coding.BDL26CoboundaryContainment
