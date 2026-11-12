-- Prove2me | solution 1 for QEC.Coding.BDL26CoboundaryContainment.x_mass_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:24:27.645652+00:00
-- url     : https://prove2.me/submissions/8c6004d2-3e50-4ed9-95fe-685a8ef3cb93

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
theorem _root_.solution (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    pX S n β (xContainment S n τ) =
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) *
        pX S n β (FixedCoboundaryGibbs.translated (zSyndrome S n) τ) :=
  FixedCoboundaryGibbs.containment_mass_exact (zSyndrome S n) (2*β) τ
end QEC.Coding.BDL26CoboundaryContainment
