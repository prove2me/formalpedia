-- Prove2me | solution 1 for PI.WGL.XiB.nu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:34.64488+00:00
-- url     : https://prove2.me/submissions/3ab42ccb-8a40-4864-a332-627002157571

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_XiA_tele_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin N) :
    (∑ i : Fin n, ((aa h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0)) : ℕ) = lam.natW t := by
  subst h
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  apply Nat.cast_injective (R := ℤ)
  have hnat : ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.w ⟨n, by omega⟩ := by
    have hle : t ≤ ⟨n, by omega⟩ := by rw [Fin.le_def]; have := t.2; simp; omega
    have := lam.anti hle
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n + 1 by omega)]
    rw [Int.toNat_of_nonneg (by simp; omega)]
    simp
  rw [hnat]
  push_cast
  rw [Finset.sum_congr rfl (g := fun i : Fin n => (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) i.1)]
  · rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) n,
      XiA.tele_sum ℓ n t.1 (by have := t.2; omega)]
    simp only [hℓ, dif_pos t.2, dif_pos (show n < n + 1 by omega)]
  · intro i _
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    rw [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    simp only [hℓ, dif_pos (show i.1 < n + 1 by omega), dif_pos (show i.1 + 1 < n + 1 by omega)]
    by_cases hti : t.1 ≤ i.1
    · rw [if_pos (by omega), if_pos hti]
      unfold aa bb
      ring
    · rw [if_neg (by omega), if_neg hti]
      ring
end PI.WGL.XiB
