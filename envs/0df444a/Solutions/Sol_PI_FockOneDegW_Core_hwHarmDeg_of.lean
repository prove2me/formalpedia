-- Prove2me | solution 1 for PI.FockOneDegW.Core.hwHarmDeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:50.247253+00:00
-- url     : https://prove2.me/submissions/0e9593e0-959a-42a1-b5de-f443b46eea51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_coeff_zero_of_dd
import Theorems.Thm_PI_FockOneDegW_Core_core
import Theorems.Thm_P2M_PI_FockOneDegW_Core_exists_monomial_weight__7e76f9f36b77
import Theorems.Thm_PI_FockOneDegW_Core_shift_eq
import Theorems.Thm_PI_FockOneDegW_Diag_fockAct1_monomial
import Theorems.Thm_PI_FockOneDegW_Diag_wt_of_isHW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (hK : OpsK) (hL : HarmIff) : HwHarmDeg := by
  intro p q r s μ e v hv hHW hH
  obtain ⟨h0, hw⟩ := wt_of_isHW _ μ v hHW
  obtain ⟨α, hα, hdeg, hμ⟩ := exists_monomial_weight' (fun a => fockAct1 p q r s (Eab a a))
    (fun a β => W1 a β) (fun a β => fockAct1_monomial p q r s a β) μ e v hv h0 hw
  have hrow : ∀ (a : Ix p q) (c d : Ix r s), linePos ((a, c) : Ln p q r s) = false →
      linePos ((a, d) : Ln p q r s) = true → α (a, c) = 0 ∨ α (a, d) = 0 := by
    intro a c d h1 h2
    refine coeff_zero_of_dd v _ _ ?_ (core hK hL μ v hHW hH a c d h1 h2) α hα
    intro h
    rw [h] at h1
    rw [h1] at h2
    exact Bool.false_ne_true h2
  have hμ' : μ = fun b => W1 b α := funext hμ
  subst hμ'
  unfold degW
  calc (e : ℚ) = ∑ l : Ln p q r s, (α l : ℚ) := by rw [← hdeg, Nat.cast_sum]
    _ = ∑ a : Ix p q, ∑ c : Ix r s, (α (a, c) : ℚ) :=
        Fintype.sum_prod_type (fun l : Ln p q r s => (α l : ℚ))
    _ = _ := Finset.sum_congr rfl fun a _ => (shift_eq α hrow a).symm
end PI.FockOneDegW.Core
