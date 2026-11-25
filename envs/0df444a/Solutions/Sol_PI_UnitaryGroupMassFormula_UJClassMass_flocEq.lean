-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.flocEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:48.936722+00:00
-- url     : https://prove2.me/submissions/d31ad4e8-cd7c-453f-ad87-740c4ad6865d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_floc_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) (hNL : ∀ x ∈ N, (D : 𝓞 E) • x ∈ L) :
    Floc v L = Floc v N :=
  Set.Subset.antisymm (floc_le v L N D hD hLN) (floc_le v N L D hD hNL)
end PI.UnitaryGroupMassFormula.UJClassMass
