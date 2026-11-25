-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finMaxElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:21.774507+00:00
-- url     : https://prove2.me/submissions/3f116ef2-2309-42c1-b0cc-3d0e68b03950

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (a : 𝓞 E) (ha : a ≠ 0) : {p : Ideal (𝓞 E) | p.IsMaximal ∧ a ∈ p}.Finite := by
  have hI : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have hfin := (Ideal.finite_factors hI).image (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
  apply hfin.subset
  rintro p ⟨hp, hap⟩
  have hne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  refine ⟨⟨p, hp.isPrime, hne⟩, ?_, rfl⟩
  show p ∣ Ideal.span {a}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hap
end PI.UnitaryGroupMassFormula.UJClassMass
