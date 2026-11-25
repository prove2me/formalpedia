-- Prove2me | solution 1 for PI.GalTorsConj.W.conj_pow_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:50.894887+00:00
-- url     : https://prove2.me/submissions/09329697-e841-4ba9-9567-fb1cfb8e8f81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution {x x' : ℂ} (h : Cj1 M₁ ρ₁ x x') (n : ℕ) : Cj1 M₁ ρ₁ (x ^ n) (x' ^ n) := by
  obtain ⟨hx, rfl⟩ := h
  refine ⟨pow_mem hx n, ?_⟩
  rw [← map_pow]
  rfl
end PI.GalTorsConj.W
