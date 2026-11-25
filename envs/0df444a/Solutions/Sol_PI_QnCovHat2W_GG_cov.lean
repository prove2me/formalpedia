-- Prove2me | solution 1 for PI.QnCovHat2W.GG_cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:50.396622+00:00
-- url     : https://prove2.me/submissions/e7a46f36-d820-48ef-b64f-824232f70726

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Theorems.Thm_PI_QnCovHat2W_sum_rows
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL_prod_row
import Theorems.Thm_PI_QnCovHat2W_sum_sgnL_prod_col
import Theorems.Thm_PI_QnCovHat2W_sum_swap4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F F' : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (P Q : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (hLin : ∀ x y : Fin m → Fin (m + 2), F' x y =
      ∑ c : Fin m → Fin (m + 2), ∑ d : Fin m → Fin (m + 2),
        ((∏ k, P (c k) (x k)) * ∏ k, Q (y k) (d k)) • F c d)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F' (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a') = (P.det * Q.det) • GG F β β' a a' := by
  have hv : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (v ᵥ* P) i = ∑ z, v z * P z i := by
    intro v i
    simp [Matrix.vecMul, dotProduct]
  have hw : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (Q *ᵥ v) i = ∑ z, v z * Q i z := by
    intro v i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have key : ∀ c d : Fin (m + 2) → Fin (m + 2),
      (sgnL c id * sgnL d id * ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) *
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1))) •
        F' (fun k => c k.succ.succ) (fun k => d k.succ.succ) =
      ∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
    intro c d
    have e1 : ∀ x : Fin (m + 2) → Fin (m + 2),
        ∑ y : Fin (m + 2) → Fin (m + 2), (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) =
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y := by
      intro x
      rw [sum_rows (fun k z => Q (d k) z) a a' (fun y => F (fun k => x k.succ.succ) y), hw a, hw a']
    have e2 : ∑ x : Fin (m + 2) → Fin (m + 2), (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y) =
        ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) • ∑ x : Fin m → Fin (m + 2), (∏ k, P (x k) (c k.succ.succ)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y) := by
      rw [sum_rows (fun k z => P z (c k)) β β' (fun x => ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y), hv β, hv β']
    have e3 : (∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ)) =
        (sgnL c id * sgnL d id) • ∑ x : Fin (m + 2) → Fin (m + 2),
          (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) • ∑ y : Fin (m + 2) → Fin (m + 2),
            (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
              F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      congr 1
      ring
    rw [e3]
    simp_rw [e1]
    rw [e2, hLin]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring
  unfold GG
  simp_rw [key]
  rw [sum_swap4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [← Finset.sum_smul, smul_smul]
  congr 1
  have hcd : ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
      sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
        (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) =
      (∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id * ∏ k, P (x k) (c k)) *
        (∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
  rw [hcd, sum_sgnL_prod_row, sum_sgnL_prod_col]
  ring
end PI.QnCovHat2W
