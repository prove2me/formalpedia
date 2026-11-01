-- Prove2me | solution 1 for SalesTrust.Sharing.static_benchmark
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:28:54.396001+00:00
-- url     : https://prove2.me/submissions/a9448fba-e339-4d83-9dfd-011622bdefae

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model
import Theorems.Thm_SalesTrust_Sharing_proposition_1

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) :
    IsOptimalS P (menuS P) ∧ (∀ m, IsOptimalS P m → m = menuS P) ∧
      retailerProfit P (menuS P) = staticRent P := by
  set P0 : Params := ⟨P.p, P.VH, P.VL, 0⟩ with hP0
  have hS0 : P0.Standing := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hS
    exact ⟨h1, h2, h3, h4, le_refl _, by norm_num⟩
  have hfe : ∀ m, FeasibleS P m ↔ FeasibleNE P0 m := by
    intro m
    simp only [FeasibleS, FeasibleNE, IRS, IRD, ICS, punish, cont, hP0]
    simp
  have hmf : ∀ m, mfrProfit P0 m = mfrProfit P m := fun m => rfl
  have hmenu : menuNE P0 = menuS P := by
    simp only [menuNE, menuS, hP0]
    ext <;> simp [qSL, TSH, TSL]
  have hopt : ∀ m, IsOptimalS P m ↔ IsOptimalNE P0 m := by
    intro m
    simp only [IsOptimalS, IsOptimalNE, hfe, hmf]
  obtain ⟨h1, h2⟩ := proposition_1 P0 hS0
  refine ⟨?_, ?_, ?_⟩
  · rw [hopt, ← hmenu]; exact h1
  · intro m hm
    rw [← hmenu]; exact h2 m ((hopt m).mp hm)
  · obtain ⟨hp0, hp1, -, -, -, -⟩ := hS
    have h1 : (1 - P.p) ≠ 0 := by linarith
    simp only [retailerProfit, staticRent, gap, menuS, piR, qSL, TSH, TSL]
    field_simp
    ring
