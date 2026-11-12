-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.commute_goodJoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:08:53.307345+00:00
-- url     : https://prove2.me/submissions/3cdf98b5-3ddd-4afb-9266-ad9b56235d14

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_commute_rectangle_iff

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
    (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (coupling S n q a) (Pjoint S n BX BZ) ↔
      BXᶜ = ∅ ∨ BZᶜ = ∅ ∨
        (translatedX S n q a BXᶜ = BXᶜ ∧ translatedZ S n q a BZᶜ = BZᶜ) :=
  commute_rectangle_iff S n q a BXᶜ BZᶜ
end QEC.Coding.BDL26SectorTranslation
