-- Prove2me | solution 1 for QFlexSC.ZeroInv.proj_succ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:26:24.240387+00:00
-- url     : https://prove2.me/submissions/90507dc6-10c7-4dcc-aeb0-4290ded4354b

import Definitions.Def_QFlexSC_ZeroInv_Model

set_option autoImplicit false
open QFlexSC.ZeroInv

theorem solution (P : QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ) (j : ℕ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1)
    (hf : 0 ≤ f j)
    (hl : proj P Iprev rprev f j = 0)
    (hr : mcStep P Iprev rprev f j = f j) :
    proj P Iprev rprev f (j + 1) = 0 := by
  have hlo : 1 - Ωcum P.ωin j ≤ 1 := by
    simp only [Ωcum, sub_sub_cancel]
    apply Finset.prod_le_one
    · intro q hq
      linarith [(hstd q (Finset.mem_Icc.mp hq).1).2.2]
    · intro q hq
      linarith [(hstd q (Finset.mem_Icc.mp hq).1).2.1]
  have hup : 1 ≤ 1 + Acum P.αout j := by
    have h := Finset.one_le_prod (s := Finset.Icc 1 j) (f := fun q => 1 + P.αout q)
      (fun q hq => by linarith [(hstd q (Finset.mem_Icc.mp hq).1).1])
    unfold Acum
    linarith
  change max 0 (proj P Iprev rprev f j +
    (1 - Ωcum P.ωin j) * mcStep P Iprev rprev f j -
    (1 + Acum P.αout j) * f j) = 0
  rw [hl, hr]
  apply max_eq_left
  nlinarith [mul_le_mul_of_nonneg_right hlo hf, mul_le_mul_of_nonneg_right hup hf]

#print axioms solution
