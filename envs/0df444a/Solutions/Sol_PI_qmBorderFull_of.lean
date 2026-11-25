-- Prove2me | solution 1 for PI.qmBorderFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:33.2475+00:00
-- url     : https://prove2.me/submissions/2bcc368b-6501-43fa-a4c3-5a496914cb70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_QmBorderFullOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_Tm_of_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_bfCross_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_mid_comp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_mid_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_rowPart
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_zmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bL_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_borderFull_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_tm_comm_E

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI
private theorem snoc_comp_cast_eq_bS_of_eq {n k t : ℕ} (hk : k = t) (h : t + 1 = k + 1) (f : Fin k → Fin n)
    (g : Fin t → Fin n) (es : Fin n) (hfg : ∀ i : Fin k, f i = g (Fin.cast hk i)) :
    (Fin.snoc f es ∘ Fin.cast h : Fin (t + 1) → Fin n) = bS g es := by
  subst hk
  have hf : f = g := funext fun i => by simpa using hfg i
  subst hf
  funext i
  simp [bS]
private theorem bfMid_of_expLastCol_expLastRow_skipSucc_bfCross (hLC : ExpLastCol) (hLR : ExpLastRow) (hS1 : SkipSucc)
    (hX : UnitaryGroupMassFormula.QmBorderFull.BFCross) : UnitaryGroupMassFormula.QmBorderFull.BFMid := by
  intro A _ _ n m E e es v hG hB u w
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by have := w.pos; omega⟩
  have hexp := hLC A n (t + 1) E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bS v es) (u - 1)
  have hb1 : bS v es ∘ Fin.castSucc = v := by
    funext i
    simp [bS]
  have hb2 : bS v es (Fin.last (t + 1)) = es := by simp [bS]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hexp
  beta_reduce at hexp
  rw [hb1, hb2, Fin.succ_last, hX A n t E e es v hG hB u w, UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp] at hexp
  simp only [Nat.succ_eq_add_one] at hexp
  have e1 : bE e (bS (v ∘ w.succAbove) es) ∘ Fin.succ = bS (v ∘ w.succAbove) es := by
    funext i
    simp [bE]
  have e2 : bE e (bS (v ∘ w.succAbove) es) 0 = e := by simp [bE]
  have e3 : bE e (bS (v ∘ w.succAbove) es) (Fin.last (t + 1)) = es := by
    rw [← Fin.succ_last]
    simp [bE, bS]
  have hees : e ≠ es := hB.2.1
  rw [Fin.succAbove_zero, e1, e2, e3, UnitaryGroupMassFormula.QmBorderFull.bL_last,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E _ hees,
    UnitaryGroupMassFormula.QmBorderFull.Four.rowPart hLR E hG e (v ∘ w.succAbove) v (fun x => hB.2.2.1 x) (u - 1)] at hexp
  have g1 : bE e (bS v es) ∘ Fin.succ = bS v es := by
    funext i
    simp [bE]
  have g2 : bE e (bS v es) 0 = e := by simp [bE]
  have hsk : ∀ i : Fin (t + 1), (v ∘ skip1 i : Fin t → Fin n) = v ∘ i.succAbove := by
    intro i
    funext j
    exact congrArg v (hS1 t i j)
  have hu1 : u - 1 - 1 = u - 2 := by ring
  have hu2 : u - 1 - ((t + 1 : ℕ) : ℂ) = u - ((t + 1 : ℕ) : ℂ) - 1 := by ring
  rw [UnitaryGroupMassFormula.QmBorderFull.Four.mid_val (t := t + 1) e es v w, g2,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E u (hB.2.2.1 w), UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp, g1, hexp]
  rw [hu1, hu2]
  simp only [hsk, Fin.val_succ, Fin.coe_castSucc, Fin.val_zero, Fin.val_last]
  rw [snoc_comp_cast_eq_bS_of_eq (k := t + 1 - 1) (t := t) rfl _ (v ∘ w.succAbove) (v ∘ w.succAbove) es (fun _ => rfl)]
  have hT : ∀ x : Fin (t + 1), E e (v x) * Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es =
      Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es * E e (v x) := fun x =>
    (UnitaryGroupMassFormula.QmBorderFull.tm_comm_E E hG _ es e (v x) hees.symm (hB.2.2.2 x)).symm
  clear hexp hb1 hb2 e1 e2 e3 g1 g2 hu1 hu2 hX hLC hLR hS1 hsk
  simp only [UnitaryGroupMassFormula.QmBorderFull.Four.zmul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_add,
    Finset.mul_sum, Finset.smul_sum, Finset.sum_mul, mul_ite, mul_zero, smul_ite, smul_zero, mul_assoc, hT]
  have k1 : ((-1 : ℤ) ^ (t + 1 + 0) * (-1) ^ ((w : ℕ) + 1)) = (-1) ^ ((w : ℕ) + 1 + (t + 1)) := by ring
  have k2 : ∀ a b : ℤ, a * (b * ((-1) ^ (w : ℕ) * (-1) ^ ((w : ℕ) + 1))) = -(a * b) := by
    intro a b
    have hw : ((-1 : ℤ) ^ (w : ℕ)) * (-1) ^ ((w : ℕ) + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hw]
    ring
  have k3 : ∀ x : ℕ, (-1 : ℤ) ^ x * ((-1) ^ (t + 1 + (t + 1)) * (-1) ^ ((w : ℕ) + 1)) = -(-1) ^ ((w : ℕ) + x) := by
    intro x
    have : ((-1 : ℤ) ^ (t + 1 + (t + 1))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [this]
    ring
  have kite : ∀ (c : Prop) [Decidable c] (X : A), (if c then -X else 0) = -(if c then X else 0) := by
    intro c _ X
    split_ifs <;> simp
  simp only [k1, k2, k3, neg_smul, kite, Finset.sum_neg_distrib]
  abel
end PI
end

set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution (hES : PI.QmBorderES) (hCol : PI.QmColExp) (hRow : PI.QmRowExp) (hSkip : PI.QmSkip) :
    PI.QmBorderFull := by
  obtain ⟨hE, hS⟩ := hES
  obtain ⟨hFC, hLC⟩ := hCol
  obtain ⟨hFR, hLR⟩ := hRow
  obtain ⟨hS1, hS2⟩ := hSkip
  exact UnitaryGroupMassFormula.QmBorderFull.borderFull_of hFC hS
    (bfMid_of_expLastCol_expLastRow_skipSucc_bfCross hLC hLR hS1 (UnitaryGroupMassFormula.QmBorderFull.Four.bfCross_of ⟨hFR, hLR⟩ ⟨hS1, hS2⟩))
end PI
