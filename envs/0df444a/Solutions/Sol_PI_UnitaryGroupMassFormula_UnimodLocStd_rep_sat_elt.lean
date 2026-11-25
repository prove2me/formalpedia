-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:54.842477+00:00
-- url     : https://prove2.me/submissions/f0e00503-a98f-4df0-ba66-52ae3ebfb0ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_theta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_rat


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
theorem _root_.solution {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) (n c s : ℤ) (hs : ¬ (l : ℤ) ∣ s) :
    SatMem l Λ ((((n : ℂ) - c * conj (cmTheta b d)) / s) • v) := by
  have hconj : conj (cmTheta b d) = b - cmTheta b d := by
    unfold cmTheta
    simp only [map_div₀, map_add, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have e : (((n : ℂ) - c * conj (cmTheta b d)) / s) • v =
      (((n - c * b : ℤ) : ℂ) / s) • v + ((c : ℂ) / s) • (cmTheta b d • v) := by
    rw [hconj, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact rep_sat_add (l := l) (Λ := Λ) hl (rep_sat_rat (l := l) (Λ := Λ) hl hv _ s hs) (rep_sat_rat (l := l) (Λ := Λ) hl (rep_sat_theta l Λ hθ hv) c s hs)
end PI.UnitaryGroupMassFormula.UnimodLocStd
