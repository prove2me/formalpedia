-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:24:45.275017+00:00
-- url     : https://prove2.me/submissions/d920fd1b-b9e3-4e74-9064-e683d2db7053

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (cmTheta b d • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm]
  exact hθ _ hv
end PI.UnitaryGroupMassFormula.UnimodLocStd
