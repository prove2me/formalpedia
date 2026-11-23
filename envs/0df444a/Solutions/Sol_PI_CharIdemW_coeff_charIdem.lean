-- Prove2me | solution 1 for PI.CharIdemW.coeff_charIdem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:07.907814+00:00
-- url     : https://prove2.me/submissions/1aabd36b-5e3c-4efa-aa83-6fa405aeef50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (V : FDRep ℂ G) (g : G) :
    (charIdem V).coeff g =
      ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹ := by
  classical
  unfold PI.CharIdem.charIdem
  simp [Finsupp.single_apply]
end PI.CharIdemW
