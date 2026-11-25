-- Prove2me | solution 1 for PI.DatumBlockEigen.Main.phiU_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:13.617547+00:00
-- url     : https://prove2.me/submissions/c7ddecbb-15d4-42bc-bdb2-1dbb535b1131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
namespace PI.DatumBlockEigen.Main
theorem _root_.solution (ρ : J' →* ℂˣ) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F)
    (h : ¬ Supp O ϖ J' x) : phiU O ϖ J' ρ x = 0 := by
  unfold phiU
  exact dif_neg h
end PI.DatumBlockEigen.Main
