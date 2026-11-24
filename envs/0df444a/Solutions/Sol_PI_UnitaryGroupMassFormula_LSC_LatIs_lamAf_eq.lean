-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:17:27.955124+00:00
-- url     : https://prove2.me/submissions/7a1407bf-bf87-48c9-a28b-7e83281ef235

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC
open PI.UnitaryGroupMassFormula.LSC.LatIs
namespace PI.UnitaryGroupMassFormula.LSC.LatIs
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) :
    I.Lf = Formalism.UG.latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.MainNotions.S.IntAf I.F I.E) I.L := by
  show Formalism.MainNotions.S.lamAf (F := I.F) I.L = _
  unfold Formalism.MainNotions.S.lamAf Formalism.UG.latS
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
end PI.UnitaryGroupMassFormula.LSC.LatIs
