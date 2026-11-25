-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.sat_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:44.086578+00:00
-- url     : https://prove2.me/submissions/2bc3e3d4-a1c8-4aeb-acc6-1207df39c4cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_H_nsmul_nsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_self_int


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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
variable {a b c d ha hd lam hlam m}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) :
    ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧ stdH (cmL a b d ha hd lam hlam) m v v = repKappa a b d ha hd lam hlam * p / q := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨n, hn⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  refine ⟨n, (s : ℤ) * s, not_dvd_mul' hl hs' hs', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn
end PI.UnitaryGroupMassFormula.UnimodLocStd
