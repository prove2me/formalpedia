-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.bad_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:54:30.14423+00:00
-- url     : https://prove2.me/submissions/1bead1f1-4503-4f96-9f88-24d8266c094c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_compl
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_eq_badProjector


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25
namespace QEC.Coding.BDL26TwoSectorBadProjector
theorem _root_.solution (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    1 - Pjoint S n BX BZ =
      CSSGibbs.badProjector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
        (badUnionWords S n BX BZ) := by
  unfold badUnionWords
  rw [← CSSGibbs.selectedProjector_eq_badProjector,
    CSSGibbs.selectedProjector_compl]
  rfl
end QEC.Coding.BDL26TwoSectorBadProjector
