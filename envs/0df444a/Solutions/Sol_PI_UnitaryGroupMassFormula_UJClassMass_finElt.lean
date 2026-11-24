-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.finElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:57:37.113163+00:00
-- url     : https://prove2.me/submissions/77015f03-2b32-43c9-9944-a3d8c85d062b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (m : 𝓞 F) (hm : m ≠ 0) : {w : HeightOneSpectrum (𝓞 F) | m ∈ w.asIdeal}.Finite := by
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  apply (Ideal.finite_factors hI).subset
  intro w hw
  show w.asIdeal ∣ Ideal.span {m}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw
end PI.UnitaryGroupMassFormula.UJClassMass
