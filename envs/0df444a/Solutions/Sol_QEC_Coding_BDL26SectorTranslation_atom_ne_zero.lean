-- Prove2me | solution 1 for QEC.Coding.BDL26SectorTranslation.atom_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:52:12.731204+00:00
-- url     : https://prove2.me/submissions/ddb61e82-5c3e-4aaa-9a62-79fd3b016d0a

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_realizable_projector_trace_two


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
theorem _root_.solution (s : JointImage S n) :
    projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) ≠ 0 := by
  intro h
  have ht := realizable_projector_trace_two S n s.1 s.2
  change LinearMap.trace ℂ _ (projector S n
    (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s)) = (2 : ℂ) at ht
  rw [h, map_zero] at ht
  norm_num at ht
end QEC.Coding.BDL26SectorTranslation
