-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:18:26.03384+00:00
-- url     : https://prove2.me/submissions/a4f28609-0ab8-4eb4-aaa7-fc92c0666348

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    pZ S n β (zContainment S n τ) ≤ Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.containment_mass_le (xSyndrome S n) (2*β) τ
end QEC.Coding.BDL26CoboundaryContainment
