-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_symm_aa89fdc4ec16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:04.637416+00:00
-- url     : https://prove2.me/submissions/15aefa3b-083b-494e-a571-df5616d3b3ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {R : Type*} [CommSemiring R] (f : MvPolynomial (Σ k', ι' k') R) :
    rename (splitVar j ι') (rename (splitVarEquiv j ι').symm f) = f := by
  show rename (splitVarEquiv j ι') (rename (splitVarEquiv j ι').symm f) = f
  rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers
