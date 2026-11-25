-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.exists_good_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:43.220875+00:00
-- url     : https://prove2.me/submissions/a7f9a30e-ff76-461a-b3d1-eec7b2e29151

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨hE, _, _, hd⟩ := hok
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  norm_num at h1 h2 h3
  have hb : (l : ℤ) ∣ b := by
    have h4 := dvd_sub (dvd_sub h3 h1) h2
    have e : (a : ℤ) + b + c - a - c = b := by ring
    rwa [e] at h4
  have hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ) := by
    have e : (d : ℤ) = 4 * a * c - b ^ 2 := by linarith
    rw [e]
    refine dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)
    rw [pow_two]
    exact mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2
  have hl2' : l ^ 2 ∣ d := by exact_mod_cast hl2
  have hld : l ∣ d := (dvd_pow_self l two_ne_zero).trans hl2'
  have hleq : l = d := (Nat.prime_dvd_prime_iff_eq hl hd).mp hld
  subst hleq
  have h5 := Nat.le_of_dvd hd.pos hl2'
  have h6 := hd.two_le
  nlinarith
end PI.UnitaryGroupMassFormula.UnimodLocStd
