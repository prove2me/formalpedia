-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.tail_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:56:32.894956+00:00
-- url     : https://prove2.me/submissions/aa4f41c4-be10-4658-a1d6-8b8ad4c81bb0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pX_bounds
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_pZ_bounds
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_exact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    0 ≤ clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) := by
  rw [tail_exact]
  have hx := pX_bounds S n β BX
  have hz := pZ_bounds S n β BZ
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hz.2)]
end QEC.Coding.BDL26TwoSectorBadProjector
