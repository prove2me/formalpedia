-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChange_kleimanNef_field_of_alt_620a843bea6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:26.905401+00:00
-- url     : https://prove2.me/submissions/e8af63d9-36a0-4cbf-b41f-87de53941cca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_finiteDimensional_0e42da5ad978
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_aAt_of_bAt_bab6f562c0e5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt
universe u v
noncomputable section
set_option linter.unusedSectionVars false
open LocalChangeEq
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
namespace LocalChange
theorem _root_.solution (hB : LocalChange.Statement.{u}) :
    GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ Nm M₁ M₂ g hg hloc
  have : FiniteDimensional K V := finiteDimensional M₁
  exact aAt_of_bAt (Module.finBasis K V).equivFun (hB K _) Nm M₁ M₂ g hg hloc
end LocalChange
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
