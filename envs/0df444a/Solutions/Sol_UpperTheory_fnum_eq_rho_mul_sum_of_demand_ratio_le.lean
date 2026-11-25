-- Prove2me | solution 1 for UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:59:01.947645+00:00
-- url     : https://prove2.me/submissions/1942e88d-fda0-470e-99b8-7c92e4c1bf03

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_FnumEqRhoMulSumOfDemandRatioLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Formalism.IncomingBounds
namespace UpperTheory.AlternatingNumberFlow
section Helpers
variable {l d : ℕ} [NeZero d]
private lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i :=
  (Finset.mem_filter.1 hi).2.pos
private lemma one_mem_oddLevels {d : ℕ} (hd : 2 ≤ d) : 1 ∈ oddLevels d :=
  Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), odd_one⟩
private lemma gam_sub_inv (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
  unfold gam rho
  field_simp
  ring
private lemma sum_incoming (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun s => x s i)
private lemma flowVal_mul_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    ((l : ℝ) + 1) * flowVal d x ≤ ∑ s, D s := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : ∑ s : ZMod d, ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i) ≤ ∑ s, D s :=
    Finset.sum_le_sum fun s _ => hx.2 s
  rw [Finset.sum_add_distrib, sum_incoming] at h1
  refine le_trans ?_ h1
  unfold flowVal
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hx0 := hx.1 s i
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl' (oddLevels_one_le hi)
  nlinarith [mul_nonneg (sub_nonneg.2 hli) hx0]
private lemma zero_isFlow {D : ZMod d → ℝ} (hD : 0 ≤ D) : IsFlow l d D (0 : ZMod d → ℕ → ℝ) :=
  ⟨fun _ _ => le_refl _, fun s => by simpa using hD s⟩
private lemma maxFlow_le (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    maxFlow l d D ≤ (∑ s, D s) / ((l : ℝ) + 1) := by
  have hpos : (0 : ℝ) < l + 1 := by positivity
  apply csSup_le
  · exact ⟨0, (0 : ZMod d → ℕ → ℝ), zero_isFlow hD, by simp [flowVal]⟩
  · rintro t ⟨x, hx, rfl⟩
    rw [le_div_iff₀ hpos]
    linarith [flowVal_mul_le hl hx]
private lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  have hpos : (0 : ℝ) < l + 1 := by positivity
  apply le_csSup
  · refine ⟨(∑ s, D s) / ((l : ℝ) + 1), ?_⟩
    rintro t ⟨y, hy, rfl⟩
    rw [le_div_iff₀ hpos]
    linarith [flowVal_mul_le hl hy]
  · exact ⟨x, hx, rfl⟩
private lemma altNum_rec (hl : 1 ≤ l) (D : ZMod d → ℝ) (s : ZMod d) :
    (l : ℝ) * altNum l d D s + altNum l d D (s - 1) = (1 - ((l : ℝ) ^ (2 * d))⁻¹) * D s := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  set a : ℕ → ℝ := fun r => (-1 : ℝ) ^ r * ((l : ℝ) ^ r)⁻¹ * D (s - (r : ZMod d)) with ha
  have h1 : (l : ℝ) * altNum l d D s = ∑ r ∈ Finset.range (2 * d), a r := by
    unfold altNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ha]
    rw [pow_succ]
    field_simp
  have h2 : altNum l d D (s - 1) = -∑ r ∈ Finset.range (2 * d), a (r + 1) := by
    unfold altNum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [ha]
    have : s - 1 - (r : ZMod d) = s - ((r + 1 : ℕ) : ZMod d) := by push_cast; ring
    rw [this, pow_succ (-1 : ℝ) r]
    ring
  rw [h1, h2, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have h3 : ((2 * d : ℕ) : ZMod d) = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  simp only [ha, pow_zero, inv_one, Nat.cast_zero, sub_zero, h3, (even_two_mul d).neg_one_pow]
  ring
private lemma sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), f r = ∑ u ∈ Finset.range m, (f (2 * u) + f (2 * u + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring
private lemma altNum_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ}
    (hr : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) (s : ZMod d) : 0 ≤ altNum l d D s := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  unfold altNum
  rw [sum_range_two_mul]
  refine Finset.sum_nonneg fun u _ => ?_
  have hB := hr (s - ((2 * u : ℕ) : ZMod d)) (s - ((2 * u + 1 : ℕ) : ZMod d))
  have hP : 0 < ((l : ℝ) ^ (2 * u + 1))⁻¹ := by positivity
  rw [(show Even (2 * u) from ⟨u, by ring⟩).neg_one_pow,
    (show Odd (2 * u + 1) from ⟨u, rfl⟩).neg_one_pow, pow_succ (l : ℝ) (2 * u + 1), mul_inv]
  have key : ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d)) ≤
      ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) := by
    calc ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * D (s - ((2 * u + 1 : ℕ) : ZMod d))
        ≤ ((l : ℝ) ^ (2 * u + 1))⁻¹ * (l : ℝ)⁻¹ * ((l : ℝ) * D (s - ((2 * u : ℕ) : ZMod d))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = ((l : ℝ) ^ (2 * u + 1))⁻¹ * D (s - ((2 * u : ℕ) : ZMod d)) := by
          field_simp
  linarith
end Helpers
end UpperTheory.AlternatingNumberFlow
end

set_option autoImplicit false
open scoped BigOperators
open Formalism.IncomingBounds
open UpperTheory.AlternatingNumberFlow
namespace UpperTheory
theorem _root_.solution :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) → Fnum l d D = rho l * (∑ s : ZMod d, D s) := by
  intro l d _ hl hd D hD0 hr
  have hD : 0 ≤ D := fun a => hD0 a
  have hr' : ∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s := fun s s' => hr s s'
  have hl1 : 1 ≤ l := by omega
  have hl' : (1 : ℝ) < l := by exact_mod_cast (show 1 < l by omega)
  have hlpos : (0 : ℝ) < l + 1 := by linarith
  have hden : 0 < 1 - ((l : ℝ) ^ (2 * d))⁻¹ := by
    have : 1 < (l : ℝ) ^ (2 * d) := one_lt_pow₀ hl' (by omega)
    have : ((l : ℝ) ^ (2 * d))⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  set c := 1 - ((l : ℝ) ^ (2 * d))⁻¹ with hc
  set y : ZMod d → ℝ := fun s => altNum l d D s / c with hy
  set x : ZMod d → ℕ → ℝ := fun s i => if i = 1 then y s else 0 with hx
  have hyrec : ∀ s, (l : ℝ) * y s + y (s - 1) = D s := by
    intro s
    simp only [hy]
    have := altNum_rec hl1 D s
    field_simp
    linarith
  have h1mem := one_mem_oddLevels hd
  have hflow : IsFlow l d D x := by
    refine ⟨fun s i => ?_, fun s => ?_⟩
    · simp only [hx]
      split_ifs
      · exact div_nonneg (altNum_nonneg hl1 hr' s) hden.le
      · exact le_refl _
    · simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', if_pos h1mem, pow_one, Nat.cast_one]
      rw [hyrec s]
  have hval : ((l : ℝ) + 1) * flowVal d x = ∑ s, D s := by
    have hfv : flowVal d x = ∑ s, y s := by
      unfold flowVal
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hx, Finset.sum_ite_eq', if_pos h1mem]
    have hsh : ∑ s, y (s - 1) = ∑ s, y s := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [hfv, ← Finset.sum_congr rfl fun s _ => hyrec s, Finset.sum_add_distrib, hsh,
      ← Finset.mul_sum]
    ring
  have hmax : maxFlow l d D = (∑ s, D s) / ((l : ℝ) + 1) := by
    apply le_antisymm (maxFlow_le hl1 hD)
    rw [← hval, mul_div_cancel_left₀ _ hlpos.ne']
    exact le_maxFlow hl1 hflow
  unfold Fnum
  rw [hmax, ← gam_sub_inv (by omega)]
  ring
end UpperTheory
