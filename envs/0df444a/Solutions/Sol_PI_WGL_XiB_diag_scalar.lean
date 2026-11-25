-- Prove2me | solution 1 for PI.WGL.XiB.diag_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:10.555047+00:00
-- url     : https://prove2.me/submissions/9ca4043d-f726-4a31-b301-aecc68f24643

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_teleM
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
    (s : Fin N → ℂˣ) :
    detPow ℂ N (diagGL ℂ N s) lam.detShift * XiA.xiScal h lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) := by
  subst h
  set v : ℕ → ℂˣ := fun p => if hp : p < n + 1 then s ⟨p, hp⟩ else 1 with hv
  set P : ℕ → ℂˣ := fun k => ∏ p ∈ Finset.range k, v p with hP
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  set σ : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ else 0 with hσ
  set w : ℂˣ := s ⟨n, by omega⟩ with hw
  have hPa : ∀ k (hk : k ≤ n + 1), ∏ p : Fin k, s (Fin.castLE hk p) = P k := by
    intro k hk
    show ∏ p : Fin k, s (Fin.castLE hk p) = ∏ p ∈ Finset.range k, v p
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have : p.1 < n + 1 := by omega
    simp only [hv, dif_pos this]
    rfl
  have hPs : ∀ k, P (k + 1) = P k * v k := fun k => by simp only [hP, Finset.prod_range_succ]
  have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ (n + 1) s) = P n * w := by
    ext
    have e := hPa (n + 1) le_rfl
    simp only [Fin.castLE_rfl, id] at e
    rw [hPs, show v n = w by simp [hv, hw]] at e
    rw [← e]
    simp [diagGL, Matrix.det_diagonal]
  have hshift : lam.detShift = ℓ n := by
    simp [DomWeight.detShift, hℓ]
  have hx : XiA.xiScal rfl lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      ((∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) : ℂˣ) : ℂ) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) n]
    unfold XiA.xiScal
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    have e1 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (Fin.castLE (by omega) p)
        (Fin.castLE (by omega) p) = ((P (i.1 + 1) : ℂˣ) : ℂ) := by
      rw [← hPa (i.1 + 1) (by omega), Units.coe_prod]
      simp [Matrix.diagonal_apply_eq]
    have e2 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (rowsZ rfl i p) (rowsZ rfl i p) =
        ((P i.1 * w : ℂˣ) : ℂ) := by
      simp only [Matrix.diagonal_apply_eq]
      rw [Fin.prod_univ_castSucc, ← hPa i.1 (by omega), Units.val_mul, Units.coe_prod]
      congr 1
      · refine Finset.prod_congr rfl (fun p _ => ?_)
        have : (Fin.castSucc p).1 ≠ i.1 := by simp; omega
        simp only [rowsZ, this, if_false]
        rfl
      · simp only [rowsZ, Fin.val_last, if_true, hw]
        congr 2
    rw [e1, e2, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    congr 2
    · simp [aa, hσ, hℓ, hi]
    · simp [bb, hσ, hℓ, hi]
  have htarget : ((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) =
      (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
        w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
    congr 1
    · rw [← Fin.prod_univ_eq_prod_range (fun j => (P (j + 1) / P j) ^ σ j) n]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have hj := j.2
      rw [hPs, mul_div_cancel_left]
      simp [hv, hσ, hj, show j.1 < n + 1 by omega]
    · congr 1
      unfold degZ wsum
      rw [← Fin.sum_univ_eq_sum_range ℓ (n + 1), ← Fin.sum_univ_eq_sum_range σ n]
      congr 1
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hℓ]; rw [dif_pos p.2]
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hσ]; rw [dif_pos p.2]
  unfold detPow
  rw [hx, hdet, hshift, htarget, ← Units.val_mul, teleM n P (by simp [hP]) w ℓ σ]
end PI.WGL.XiB
