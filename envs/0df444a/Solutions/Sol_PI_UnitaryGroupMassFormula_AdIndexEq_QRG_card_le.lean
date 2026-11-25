-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:47.937926+00:00
-- url     : https://prove2.me/submissions/566d1192-a389-4154-9f29-1b7a138f6455

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_zero_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution {m : ℕ} (f : Fin m → Fin n → K)
    (hf : ∀ i, H σ J (f i) (f i) ≠ 0) (ho : ∀ i j, i ≠ j → H σ J (f i) (f j) = 0) : m ≤ n := by
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (H σ J (f j)) hg
    rw [H_sum_right, H_zero_right] at h1
    simp_rw [H_smul_right] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hf j)
  have h2 := hli.fintype_card_le_finrank
  simpa using h2
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
