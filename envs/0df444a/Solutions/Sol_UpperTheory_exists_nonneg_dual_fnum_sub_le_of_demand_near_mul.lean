-- Prove2me | solution 1 for UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:05.436606+00:00
-- url     : https://prove2.me/submissions/f9756531-618d-4c80-a7b2-93a1927def27

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsMaxFlowAttainedAndIsOptDual
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_SumDemandFilterTwoDivLeOfIsOptDual
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsNonnegDualFnumSubLeOfDemandNearMul
import Theorems.Thm_UpperTheory_exists_maxFlow_attained_and_isOptDual
import Theorems.Thm_UpperTheory_sum_demand_filter_two_div_le_of_isOptDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.IncomingBounds
namespace UpperTheory
theorem _root_.solution :
    ∀ (l d : ℕ) [NeZero d], 5 ≤ l → 2 ≤ d → ∀ (κ : ℝ) (w D : ZMod d → ℝ), 0 < κ → (∀ s, 0 ≤ w s) →
    (∀ s, κ * w s ≤ D s ∧ D s ≤ κ * w s + 4 * w s) →
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧ IsDualAll l d sig ∧
      Fnum l d (fun s => κ * w s) - κ * (∑ s, w s) / (l : ℝ) ^ 3 - 8 * (∑ s, w s) / l ≤ ∑ s, D s * (gam l - sig s) := by
  intro l d _ hl hd κ w D hκ hw hD
  have hl3 : 3 ≤ l := by omega
  have hlR : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hκw : (0 : ZMod d → ℝ) ≤ fun s => κ * w s := fun s => mul_nonneg hκ.le (hw s)
  obtain ⟨-, sig, hdual, hF⟩ := UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl3 (fun s => κ * w s) hκw
  have hheavy := UpperTheory.sum_demand_filter_two_div_le_of_isOptDual l d hl3 (fun s => κ * w s) sig hκw ⟨hdual, hF⟩
  set c : ℝ := 1 / (l : ℝ) ^ 3 with hc
  have hc0 : 0 < c := by positivity
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hdual.1 s).1
  have hsig1 : ∀ s, sig s ≤ 1 := fun s => (hdual.1 s).2
  have hgam1 : 1 / (l : ℝ) ≤ gam l := by
    unfold gam
    have hden : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_le_div_iff₀ hl0 hden]
    nlinarith
  have hgam0 : 0 ≤ gam l := le_trans (by positivity) hgam1
  have hc2 : c < 2 / (l : ℝ) := by
    rw [hc, div_lt_div_iff₀ (by positivity) hl0]
    have h3 : (l : ℝ) ^ 3 = l * (l * l) := by ring
    have hll : (1 : ℝ) ≤ l * l := by nlinarith
    rw [h3]
    nlinarith
  have h2l : 2 / (l : ℝ) ≤ 1 := by
    rw [div_le_one hl0]; linarith
  refine ⟨fun s => max (sig s) c, fun s => le_trans (hsig0 s) (le_max_left _ _), ?_, ?_⟩
  · intro s i hi
    by_cases hid : i < d
    · have hmem : i ∈ oddLevels d := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hid, hi⟩
      have h := hdual.2 s i hmem
      have hp : (0 : ℝ) ≤ (l : ℝ) ^ i := by positivity
      have h1 := mul_le_mul_of_nonneg_left (le_max_left (sig s) c) hp
      have h2 := le_max_left (sig (s + (i : ZMod d))) c
      linarith
    · have hi3 : 3 ≤ i := by
        obtain ⟨k, rfl⟩ := hi
        omega
      have hpow : (l : ℝ) ^ 3 ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi3
      have hlc : (l : ℝ) ^ 3 * c = 1 := by
        rw [hc]
        field_simp
      have hp3 : (0 : ℝ) ≤ (l : ℝ) ^ 3 := by positivity
      have h1 : (l : ℝ) ^ 3 * c ≤ (l : ℝ) ^ i * max (sig s) c :=
        mul_le_mul hpow (le_max_right _ _) hc0.le (le_trans hp3 hpow)
      have h2 : 0 ≤ max (sig (s + (i : ZMod d))) c := le_trans hc0.le (le_max_right _ _)
      linarith
  · have hpt : ∀ s, κ * w s * (gam l - sig s) - κ * w s * c - 4 * w s / l
        - 4 * (if 2 / (l : ℝ) ≤ sig s then w s else 0) ≤ D s * (gam l - max (sig s) c) := by
      intro s
      obtain ⟨hD1, hD2⟩ := hD s
      have hws := hw s
      have hmx : max (sig s) c - sig s ≤ c := by
        rcases le_total (sig s) c with h | h
        · rw [max_eq_right h]; linarith [hsig0 s]
        · rw [max_eq_left h]; linarith
      have hkw : κ * w s * (max (sig s) c - sig s) ≤ κ * w s * c :=
        mul_le_mul_of_nonneg_left hmx (mul_nonneg hκ.le hws)
      have hsplit : D s * (gam l - max (sig s) c) = κ * w s * (gam l - sig s)
          - κ * w s * (max (sig s) c - sig s) + (D s - κ * w s) * (gam l - max (sig s) c) := by ring
      have he0 : 0 ≤ D s - κ * w s := by linarith
      have he4 : D s - κ * w s ≤ 4 * w s := by linarith
      have h4l : 0 ≤ 4 * w s / l := by positivity
      split_ifs with hh
      · have hmx1 : max (sig s) c ≤ 1 := max_le (hsig1 s) (by linarith)
        have ht : -1 ≤ gam l - max (sig s) c := by linarith
        have hm := mul_le_mul_of_nonneg_left ht he0
        have : -(4 * w s) ≤ (D s - κ * w s) * (gam l - max (sig s) c) := by
          linarith
        linarith
      · push_neg at hh
        have hlt : max (sig s) c < 2 / (l : ℝ) := max_lt hh hc2
        have hlow : -(1 / (l : ℝ)) ≤ gam l - max (sig s) c := by
          have : 2 / (l : ℝ) = 1 / l + 1 / l := by ring
          linarith
        have hm := mul_le_mul_of_nonneg_left hlow he0
        have hil : (0 : ℝ) ≤ 1 / l := by positivity
        have hm2 := mul_le_mul_of_nonneg_right he4 hil
        have : -(4 * w s / l) ≤ (D s - κ * w s) * (gam l - max (sig s) c) := by
          have e : 4 * w s / l = 4 * w s * (1 / l) := by ring
          rw [e]
          have e2 : (D s - κ * w s) * -(1 / (l : ℝ)) = -((D s - κ * w s) * (1 / l)) := by ring
          linarith
        linarith
    have hsum := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hpt s
    simp only [Finset.sum_sub_distrib] at hsum
    rw [← Finset.mul_sum, ← Finset.sum_filter] at hsum
    have hFs : Fnum l d (fun s => κ * w s) = ∑ s, κ * w s * (gam l - sig s) := hF
    have hH : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), w s
        ≤ (∑ s, w s) / l := by
      have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), κ * w s
          = κ * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), w s :=
        (Finset.mul_sum _ _ _).symm
      have e2 : (∑ s, κ * w s) / l = κ * ((∑ s, w s) / l) := by
        rw [← Finset.mul_sum]; ring
      have h := hheavy
      rw [e1, e2] at h
      exact le_of_mul_le_mul_left h hκ
    have e3 : ∑ s, κ * w s * c = κ * (∑ s, w s) / (l : ℝ) ^ 3 := by
      rw [hc, ← Finset.sum_mul, ← Finset.mul_sum]; ring
    have e4 : ∑ s, 4 * w s / (l : ℝ) = 4 * (∑ s, w s) / l := by
      rw [Finset.mul_sum, Finset.sum_div]
    rw [e3, e4] at hsum
    have hW : 0 ≤ (∑ s, w s) / l := by
      have := Finset.sum_nonneg fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hw s
      positivity
    have e5 : 8 * (∑ s, w s) / l = 4 * (∑ s, w s) / l + 4 * ((∑ s, w s) / l) := by ring
    rw [hFs, e5]
    linarith
end UpperTheory
