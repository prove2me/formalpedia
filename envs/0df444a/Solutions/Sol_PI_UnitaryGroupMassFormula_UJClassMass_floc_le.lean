-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.floc_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:52.181503+00:00
-- url     : https://prove2.me/submissions/ede79060-ad84-4065-9bfe-b6abea4ee4e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF

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
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) : Floc v L ⊆ Floc v N := by
  rintro x ⟨s, hs, hsx⟩
  refine ⟨(D : 𝓞 F) * s, fun h => (v.isPrime.mem_or_mem h).elim hD hs, ?_⟩
  rw [map_mul, map_intCast, mul_smul]
  exact hLN _ hsx
end PI.UnitaryGroupMassFormula.UJClassMass
