-- Prove2me | solution 1 for PI.GalTorsConj.W.conj_sub_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:47.894804+00:00
-- url     : https://prove2.me/submissions/58816677-c6ed-472c-b64d-17317a4b0414

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
theorem _root_.solution {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x - y) (x' - y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.sub_mem hx hy, ?_⟩
  rw [← map_sub]
  rfl
end PI.GalTorsConj.W
