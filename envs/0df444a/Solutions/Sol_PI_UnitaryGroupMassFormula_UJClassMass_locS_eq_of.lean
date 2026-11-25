-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.locS_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:41:02.333691+00:00
-- url     : https://prove2.me/submissions/bb98de33-40f7-4625-9e08-12b4f0325992

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_locS_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_locS_locS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (S : Submonoid (𝓞 E)) {X Y : Submodule (𝓞 E) V} (h1 : X ≤ locS S Y) (h2 : Y ≤ locS S X) :
    locS S X = locS S Y := le_antisymm ((locS_mono S h1).trans (locS_locS S Y).le) ((locS_mono S h2).trans (locS_locS S X).le)
end PI.UnitaryGroupMassFormula.UJClassMass
