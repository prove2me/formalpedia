-- Prove2me | solution 1 for PI.SerBridgeGLW.eOf_eq_zIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:40.973121+00:00
-- url     : https://prove2.me/submissions/fbf509ae-85aa-4b2e-bb83-b25f111d4a38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_zIdem_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {G : Type} [Group G] [Fintype G]
namespace PI.SerBridgeGLW
theorem _root_.solution (V : FDRep ℂ G) : eOf V.character = zIdem V := by
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [zIdem_coeff, eOf, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, FDRep.char_one]
  rfl
end PI.SerBridgeGLW
