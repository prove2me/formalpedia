-- Prove2me | solution 1 for RevenueOrdered.Nesting.jVal_eq_max_shifted
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:59:45.466977+00:00
-- url     : https://prove2.me/submissions/0b69fdc5-82ba-4d8c-bb1f-d95933fc2edf

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_LStar
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

set_option autoImplicit false
open RevenueOrdered.Nesting
open RevenueOrdered.Ratio (roSet noPurchase level numVals)

theorem nes_jIdx_succ {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) (hq : 1 ≤ q) (ℓ : ℕ) :
    jIdx P r (t + 1) q ℓ =
      shiftedRevenue P r (-marginalValue P r t q) ℓ + jVal P r t q := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have e1 : jIdx P r (t + 1) (q' + 1) ℓ =
      ∑ x ∈ roSet r ℓ, P x (roSet r ℓ) * (r x + jVal P r t q') +
        noPurchase P (roSet r ℓ) * jVal P r t (q' + 1) := rfl
  have e2 : marginalValue P r t (q' + 1) = jVal P r t (q' + 1) - jVal P r t q' := by
    simp [marginalValue]
  rw [e1, e2]
  unfold shiftedRevenue noPurchase
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_neg, Finset.sum_neg_distrib]
  ring

theorem nes_sup'_add {C : Type*} [Fintype C] [Nonempty C] (r : C → ℝ) (f : ℕ → ℝ) (c : ℝ) :
    (levels r).sup' (levels_nonempty r) (fun ℓ => f ℓ + c) =
      (levels r).sup' (levels_nonempty r) f + c := by
  exact (Finset.sup'_add (levels r) f c (levels_nonempty r)).symm

theorem nes_jVal_succ {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) (hq : 1 ≤ q) :
    jVal P r (t + 1) q =
      (levels r).sup' (levels_nonempty r) (shiftedRevenue P r (-marginalValue P r t q)) +
        jVal P r t q := by
  unfold jVal
  have : jIdx P r (t + 1) q = fun ℓ => shiftedRevenue P r (-marginalValue P r t q) ℓ + jVal P r t q := by
    funext ℓ; exact nes_jIdx_succ P r t q hq ℓ
  rw [this]
  exact nes_sup'_add r _ _

theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : RevenueOrdered.Nesting.IsRegular P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    jVal P r (t + 1) q =
      (levels r).sup' (levels_nonempty r) (shiftedRevenue P r (-marginalValue P r t q)) +
        jVal P r t q :=
  nes_jVal_succ P r t q hq
