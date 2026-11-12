-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.even_commute_selected_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:10:11.422331+00:00
-- url     : https://prove2.me/submissions/21e0e7d4-36eb-407c-a7ad-eaecec9da23b

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_commute_selected_iff

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
theorem _root_.solution (k : Nat) (q : Physical S (2*k)) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S (2*k))) :
    Commute (coupling S (2*k) q a) (selected S (2*k) A) ↔
      translated S (2*k) q a A = A := commute_selected_iff S (2*k) q a A
end QEC.Coding.BDL26SectorTranslation
