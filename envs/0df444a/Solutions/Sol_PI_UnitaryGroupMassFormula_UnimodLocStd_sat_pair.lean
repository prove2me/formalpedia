-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.sat_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:21.77053+00:00
-- url     : https://prove2.me/submissions/2952d832-69eb-471d-99b5-defa65c71705

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_H_nsmul_nsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_int


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
    {l : ℕ} (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) :
    ∃ n c₂ s : ℤ, ¬ (l : ℤ) ∣ s ∧ stdH (cmL a b d ha hd lam hlam) m v w =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨t, ht, htw⟩ := hw
  obtain ⟨n, c₂, hn, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv htw
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  have ht' : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => ht (by exact_mod_cast h)
  refine ⟨n, c₂, (s : ℤ) * t, not_dvd_mul' hl hs' ht', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h; apply ht; rw [show t = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn
end PI.UnitaryGroupMassFormula.UnimodLocStd
