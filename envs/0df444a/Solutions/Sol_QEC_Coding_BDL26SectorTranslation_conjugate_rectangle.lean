-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.conjugate_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:11:25.456218+00:00
-- url     : https://prove2.me/submissions/2b3771f5-906b-457c-aeca-37de87bb6cf4

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_conjugate_selected
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_translated_rectangle

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
    coupling S n q a * selected S n (A ×ˢ B) * coupling S n q a =
      selected S n (translatedX S n q a A ×ˢ translatedZ S n q a B) := by
  rw [conjugate_selected, translated_rectangle]
end QEC.Coding.BDL26SectorTranslation
