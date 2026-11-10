-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.translation_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:34:58.904281+00:00
-- url     : https://prove2.me/submissions/00172d6d-dabf-4d54-a77c-2547a1ad4cb6

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation

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
theorem _root_.solution (q : Physical S n) (s : JointImage S n) :
    translation S n q .x s = (s.1 + epsilonX S n q, s.2) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change s.2.val + xSyndrome S n 0 = s.2.val
    rw [map_zero, add_zero]
end QEC.Coding.BDL26SectorTranslation
