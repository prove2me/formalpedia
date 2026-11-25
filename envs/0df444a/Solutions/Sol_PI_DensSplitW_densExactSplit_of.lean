-- Prove2me | solution 1 for PI.DensSplitW.densExactSplit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:05.094445+00:00
-- url     : https://prove2.me/submissions/bb9e7565-e674-4d4f-977c-b9b8e84d40c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Theorems.Thm_PI_DensSplitW_count_eq
import Theorems.Thm_PI_DensSplitW_prod_factor
import Theorems.Thm_PI_DensSplitW_exp_eq
import Theorems.Thm_Formalism_L2_SG_DensExact_densSplitDisplay_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution (hF : FiberCard) : DensExactSplit := by
  intro K _ _ n m Ph Gm hPh
  rw [count_eq hF K n m Ph Gm hPh]
  have hrm : Gm.rank ≤ m := Matrix.rank_le_width Gm
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  have hqR : (0 : ℝ) < Fintype.card K := by exact_mod_cast hq0
  by_cases hmc : m + (m - Gm.rank) ≤ n
  · have hmn : m ≤ n := by omega
    rw [card_linearIndependent (K := K) (V := Fin n → K) (by rw [Module.finrank_fin_fun]; exact hmn),
      Module.finrank_fin_fun]
    rw [← densSplitDisplay_holds (Fintype.card K) n m (m - Gm.rank) hq0 hmc]
    rw [Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ n - Fintype.card K ^ i) m]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      prod_factor _ n m hq0 hmn, prod_factor _ (n - m) (m - Gm.rank) hq0 (by omega)]
    have hD : (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) =
        (Fintype.card K : ℝ) ^ (2 * n * m - m ^ 2) := by
      rw [pow_sub₀ _ hqR.ne' (by nlinarith : m ^ 2 ≤ 2 * n * m), div_eq_mul_inv]
    rw [hD, ← exp_eq n m Gm.rank hmn hrm]
    rw [pow_add, pow_add]
    have h1 : (Fintype.card K : ℝ) ^ (n * m) ≠ 0 := by positivity
    have h2 : (Fintype.card K : ℝ) ^ (Gm.rank * (n - m)) ≠ 0 := by positivity
    have h3 : (Fintype.card K : ℝ) ^ ((n - m) * (m - Gm.rank)) ≠ 0 := by positivity
    field_simp
  · have hR : densProd (Fintype.card K) 1 n m (m - Gm.rank) = 0 := by
      unfold densProd
      apply Finset.prod_eq_zero (i := 0)
      · simp only [Finset.mem_Icc]; omega
      · simp
    rw [hR]
    have hL : Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
        (Fintype.card K ^ (Gm.rank * (n - m)) *
          ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) = 0 := by
      by_cases hmn : m ≤ n
      · have : ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) = 0 :=
          Finset.prod_eq_zero (i := n - m) (Finset.mem_range.mpr (by omega)) (by simp)
        rw [this, mul_zero, mul_zero]
      · have : IsEmpty {X : Fin m → Fin n → K // LinearIndependent K X} := by
          refine ⟨fun X => ?_⟩
          have := X.2.fintype_card_le_finrank
          simp only [Fintype.card_fin, Module.finrank_fin_fun] at this
          omega
        rw [Nat.card_of_isEmpty, zero_mul]
    rw [hL]
    simp
end PI.DensSplitW
