-- Prove2me | solution 1 for QFlexSC.ZeroInv.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:26:05.955789+00:00
-- url     : https://prove2.me/submissions/9d9c7bf7-2f19-4098-b69f-a411cc5198e7

import Definitions.Def_QFlexSC_ZeroInv_Model

set_option autoImplicit false
open QFlexSC.ZeroInv

theorem solution (P : QFParams) (f : ℕ → ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αout q ∧ 0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hIR : IROut P f) :
    ∀ t j : ℕ, (1 - Ωcum P.ωout j) * f t j ≤ f (t + j) 0 ∧
      f (t + j) 0 ≤ (1 + Acum P.αout j) * f t j := by
  have hlo (j : ℕ) : 0 ≤ 1 - Ωcum P.ωout j := by
    simp only [Ωcum, sub_sub_cancel]
    exact Finset.prod_nonneg (fun q hq => sub_nonneg.mpr (hstd q (Finset.mem_Icc.mp hq).1).2.2)
  have hup (j : ℕ) : 0 ≤ 1 + Acum P.αout j := by
    have h := Finset.prod_nonneg (s := Finset.Icc 1 j) (f := fun q => 1 + P.αout q)
      (fun q hq => by linarith [(hstd q (Finset.mem_Icc.mp hq).1).1])
    unfold Acum
    linarith
  have hrlo (j : ℕ) : 1 - Ωcum P.ωout (j + 1) =
      (1 - Ωcum P.ωout j) * (1 - P.ωout (j + 1)) := by
    simp only [Ωcum, sub_sub_cancel, Finset.prod_Icc_succ_top (by omega : 1 ≤ j + 1)]
  have hrup (j : ℕ) : 1 + Acum P.αout (j + 1) =
      (1 + Acum P.αout j) * (1 + P.αout (j + 1)) := by
    unfold Acum
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ j + 1)]
    ring
  intro t j
  induction j generalizing t with
  | zero => simp [Acum, Ωcum]
  | succ j ih =>
      obtain ⟨hl, hu⟩ := ih (t + 1)
      obtain ⟨hil, hiu⟩ := hIR t j
      rw [hrlo, hrup]
      constructor
      · have h := mul_le_mul_of_nonneg_left hil (hlo j)
        simpa only [mul_assoc, Nat.add_assoc, Nat.add_comm 1 j] using h.trans hl
      · have h := mul_le_mul_of_nonneg_left hiu (hup j)
        simpa only [mul_assoc, Nat.add_assoc, Nat.add_comm 1 j] using hu.trans h

#print axioms solution
