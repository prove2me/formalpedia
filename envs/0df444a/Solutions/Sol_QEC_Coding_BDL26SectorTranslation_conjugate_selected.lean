-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.conjugate_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:38:07.878201+00:00
-- url     : https://prove2.me/submissions/ccc2199f-c45b-42b9-b503-ecf762f2acb9

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_conjugate_selected


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26SectorTranslation
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26CSSDaviesLocality BDL26TwoSectorBadProjector
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26SectorTranslation._p2m_local_instance_8726da3c88_19
attribute [local instance] QEC.Coding.BDL26SectorTranslation._p2m_local_instance_8726da3c88_20
namespace QEC.Coding.BDL26SectorTranslation
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    coupling S n q a * selected S n A * coupling S n q a =
      selected S n (translated S n q a A) :=
  CSSGibbs.pauli_conjugate_selected _ _ (row_orthogonal S n) _ A
end QEC.Coding.BDL26SectorTranslation
