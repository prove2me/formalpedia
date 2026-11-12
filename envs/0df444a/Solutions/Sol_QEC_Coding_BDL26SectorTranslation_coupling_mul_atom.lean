-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.coupling_mul_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:08:14.959231+00:00
-- url     : https://prove2.me/submissions/8dd41883-75bb-4336-abf8-39681e14ec1f

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_realizable_projector


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
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) (s : JointImage S n) :
    coupling S n q a * projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) =
      projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n)
        (translation S n q a s)) * coupling S n q a :=
  CSSGibbs.pauli_mul_realizable_projector _ _ (row_orthogonal S n) _ s
end QEC.Coding.BDL26SectorTranslation
