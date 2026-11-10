-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.translated_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:38:10.486324+00:00
-- url     : https://prove2.me/submissions/d82ba49e-d965-46d4-b35f-65d0d4c719c9

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_CSSGibbs_translatedSelection_product


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
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    translated S n q a (A ×ˢ B) = translatedX S n q a A ×ˢ translatedZ S n q a B :=
  CSSGibbs.translatedSelection_product _ _ _ A B
end QEC.Coding.BDL26SectorTranslation
