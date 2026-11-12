-- Prove2me | solution 1 for QEC.Coding.BDL26TwoSectorBadProjector.commute_XZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:54:26.997195+00:00
-- url     : https://prove2.me/submissions/b3a653fe-317f-4350-a9a9-871b2b79f4ef

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_product_XZ
import Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_product_ZX
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    Commute (PX S n BX) (PZ S n BZ) :=
  (product_XZ S n BX BZ).trans (product_ZX S n BX BZ).symm
end QEC.Coding.BDL26TwoSectorBadProjector
