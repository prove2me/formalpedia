-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.z_mass_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:24:41.52169+00:00
-- url     : https://prove2.me/submissions/5055175b-22c3-468d-a30b-01d09aefebf1

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
import Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_exact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype
namespace QEC.Coding.BDL26CoboundaryContainment
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    pZ S n β (zContainment S n τ) =
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) *
        pZ S n β (FixedCoboundaryGibbs.translated (xSyndrome S n) τ) :=
  FixedCoboundaryGibbs.containment_mass_exact (xSyndrome S n) (2*β) τ
end QEC.Coding.BDL26CoboundaryContainment
