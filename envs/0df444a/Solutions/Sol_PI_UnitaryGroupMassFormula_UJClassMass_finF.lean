-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:19.538726+00:00
-- url     : https://prove2.me/submissions/de196373-7b86-44b9-b7d3-256295bb1943

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
omit [NumberField E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (D : ℤ) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((D : 𝓞 F)) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((D : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD
  apply (Ideal.finite_factors hI).subset
  intro v hv
  show v.asIdeal ∣ Ideal.span {((D : 𝓞 F))}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv
end PI.UnitaryGroupMassFormula.UJClassMass
