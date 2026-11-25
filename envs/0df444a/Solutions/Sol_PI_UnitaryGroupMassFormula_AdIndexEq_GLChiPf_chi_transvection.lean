-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:38.443824+00:00
-- url     : https://prove2.me/submissions/ed44b302-4438-4270-9dc5-0cebf091abad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_diag_transvection
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution [CharZero k] (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (t : TransvectionStruct (Fin n) k) (h : t.toMatrix.det ≠ 0) : χ (glOf t.toMatrix h) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have key : ∀ a : k, a ≠ 0 → diagonal (Function.update (1 : Fin n → k) i a) *
      diagonal (Function.update (1 : Fin n → k) i a⁻¹) = 1 := by
    intro a ha
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx; simp [ha]
    · simp [Function.update_apply, hx]
  have key' : diagonal (Function.update (1 : Fin n → k) i 2⁻¹) *
      diagonal (Function.update (1 : Fin n → k) i 2) = 1 := by
    simpa using key 2⁻¹ (inv_ne_zero h2)
  let s : GL (Fin n) k := ⟨diagonal (Function.update (1 : Fin n → k) i 2),
    diagonal (Function.update (1 : Fin n → k) i 2⁻¹), key 2 h2, key'⟩
  have hsq : s * glOf _ h * s⁻¹ = glOf _ h * glOf _ h := by
    apply Units.ext
    change diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j c * transvection i j c
    rw [diag_transvection i j hij c, two_mul]
    symm
    apply transvection_mul_transvection_same
    all_goals exact hij
  have e := chi_conj χ s (glOf _ h)
  rw [hsq, map_mul] at e
  exact mul_left_cancel₀ (ne_of_gt (hpos _)) (e.trans (mul_one _).symm)
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
