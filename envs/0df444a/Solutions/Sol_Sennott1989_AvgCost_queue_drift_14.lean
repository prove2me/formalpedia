-- Prove2me | solution 1 for Sennott1989.AvgCost.queue_drift_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:16:53.467866+00:00
-- url     : https://prove2.me/submissions/ff30f22b-0d0c-417c-b020-750a54689ff2

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Definitions.Def_Sennott1989_AvgCost_Queue

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott8D14

open SennottDP.Discounted Sennott1989.AvgCost

variable {Act : Type} [Fintype Act] [Nonempty Act]

noncomputable def w (q : QueueData Act) (x : Act) (k : ℕ) : ℝ :=
  q.a x * q.β * (q.p k : ℝ) + (1 - q.a x * q.β) * (q.pPrev k : ℝ)

lemma trans_toReal (q : QueueData Act) (x : Act) (i k : ℕ) :
    (q.trans (i + 1) x (i + k)).toReal = w q x k := by
  have e1 : ¬ (i + k + 1 < i + 1) := by omega
  have e2 : i + k + 1 - (i + 1) = k := by omega
  have hρ0 := (q.rate_pos x).le
  have hρ1 := q.rate_lt_one x
  have h1 : (1 - q.rate x) = ENNReal.ofReal (1 - q.a x * q.β) := by
    unfold QueueData.rate
    rw [ENNReal.ofReal_sub _ hρ0, ENNReal.ofReal_one]
  simp only [QueueData.trans, show i + 1 ≠ 0 by omega, if_false, e1, e2]
  have f1 : q.rate x * (q.p k : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have f2 : ENNReal.ofReal (1 - q.a x * q.β) * (q.pPrev k : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  rw [h1, ENNReal.toReal_add f1 f2, ENNReal.toReal_mul, ENNReal.toReal_mul]
  unfold QueueData.rate w
  rw [ENNReal.toReal_ofReal hρ0, ENNReal.toReal_ofReal (by linarith)]
  simp

lemma trans_low (q : QueueData Act) (x : Act) (i j : ℕ) (hj : j < i) :
    q.trans (i + 1) x j = 0 := by
  simp [QueueData.trans, show j + 1 < i + 1 by omega]

lemma pow_bound (t : ℝ) (ht : 0 ≤ t) (m N : ℕ) (hm : m ≤ N) :
    (t + 1) ^ m ≤ 2 ^ m * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · calc (t + 1) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + t ^ N) := by
        have : 0 ≤ t ^ N := pow_nonneg ht N
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) m]
  · calc (t + 1) ^ m ≤ (2 * t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * t ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + t ^ N) := by
        have : t ^ m ≤ t ^ N := pow_le_pow_right₀ h hm
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) m]

lemma summ_S (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) :
    Summable fun k : ℕ => ((q.p k : ℝ) + (q.pPrev k : ℝ)) * (1 + (k : ℝ) ^ (q.n + 1)) := by
  have hsp : Summable fun i => (q.p i : ℝ) := (NNReal.hasSum_coe.2 q.p_hasSum).summable
  have hA : Summable fun k : ℕ => (q.p k : ℝ) * (1 + (k : ℝ) ^ (q.n + 1)) := by
    refine (hsp.add hmom).congr fun k => ?_
    ring
  have hB : Summable fun k : ℕ => (q.pPrev k : ℝ) * (1 + (k : ℝ) ^ (q.n + 1)) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (q.pPrev _).2 (by positivity))
      (fun k => ?_) (hA.mul_left (2 ^ (q.n + 2)))
    simp only [QueueData.pPrev, show k + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    have := pow_bound (k : ℝ) (by positivity) (q.n + 1) (q.n + 1) le_rfl
    push_cast
    have hp := (q.p k).2
    have h1 : (1 : ℝ) ≤ 2 ^ (q.n + 1) * (1 + (k : ℝ) ^ (q.n + 1)) := by
      have : (1 : ℝ) ≤ 2 ^ (q.n + 1) := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (q.n + 1)]
    have h2 : (1 : ℝ) + (k + 1) ^ (q.n + 1) ≤ 2 ^ (q.n + 2) * (1 + (k : ℝ) ^ (q.n + 1)) := by
      have e : (2 : ℝ) ^ (q.n + 2) = 2 * 2 ^ (q.n + 1) := by ring
      rw [e]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hp]
  exact (hA.add hB).congr fun k => by ring

lemma summ_wm (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act) (m : ℕ)
    (hm : m ≤ q.n + 1) :
    Summable fun k : ℕ => w q x k * ((k : ℝ) - 1) ^ m := by
  refine Summable.of_norm_bounded ((summ_S q hmom).mul_left (2 ^ m)) fun k => ?_
  have hρ0 := (q.rate_pos x).le
  have hρ1 := q.rate_lt_one x
  have hp := (q.p k).2
  have hpp := (q.pPrev k).2
  have hw0 : 0 ≤ w q x k := by unfold w; positivity
  have hw1 : w q x k ≤ (q.p k : ℝ) + (q.pPrev k : ℝ) := by
    unfold w; nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0, abs_pow]
  have habs : |(k : ℝ) - 1| ≤ (k : ℝ) + 1 := by
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have h1 : |(k : ℝ) - 1| ^ m ≤ ((k : ℝ) + 1) ^ m := pow_le_pow_left₀ (abs_nonneg _) habs m
  have h2 := pow_bound (k : ℝ) (by positivity) m (q.n + 1) hm
  have h3 : 0 ≤ |(k : ℝ) - 1| ^ m := by positivity
  calc w q x k * |(k : ℝ) - 1| ^ m ≤ ((q.p k : ℝ) + (q.pPrev k : ℝ)) * (2 ^ m * (1 + (k : ℝ) ^ (q.n + 1))) :=
        mul_le_mul hw1 (h1.trans h2) h3 (by positivity)
    _ = 2 ^ m * (((q.p k : ℝ) + (q.pPrev k : ℝ)) * (1 + (k : ℝ) ^ (q.n + 1))) := by ring

lemma mu1 (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act) :
    ∑' k : ℕ, w q x k * ((k : ℝ) - 1) ^ (q.n + 1 - q.n) = q.lam - q.a x * q.β := by
  rw [show q.n + 1 - q.n = 1 by omega]
  set ρ := q.a x * q.β
  have hsp : Summable fun i => (q.p i : ℝ) := (NNReal.hasSum_coe.2 q.p_hasSum).summable
  have htp : ∑' i, (q.p i : ℝ) = 1 := (NNReal.hasSum_coe.2 q.p_hasSum).tsum_eq.trans (by simp)
  have hs1 : Summable fun i : ℕ => (q.p i : ℝ) * i := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (q.p i).2 (by positivity)) (fun i => ?_) hmom
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have := pow_le_pow_right₀ h1 (show 1 ≤ q.n + 1 by omega)
      rw [pow_one] at this
      nlinarith [(q.p i).2]
  have hlam : q.lam = ∑' i : ℕ, (q.p i : ℝ) * i := by
    unfold QueueData.lam QueueData.moment; exact tsum_congr fun i => by ring
  have hA : Summable fun k : ℕ => (q.p k : ℝ) * ((k : ℝ) - 1) :=
    (hs1.sub hsp).congr fun k => by ring
  have hA' : ∑' k : ℕ, (q.p k : ℝ) * ((k : ℝ) - 1) = q.lam - 1 := by
    rw [show (fun k : ℕ => (q.p k : ℝ) * ((k : ℝ) - 1)) = fun k => (q.p k : ℝ) * k - q.p k from
      funext fun k => by ring, hs1.tsum_sub hsp, htp, hlam]
  have hBs : Summable fun k : ℕ => (q.pPrev k : ℝ) * ((k : ℝ) - 1) := by
    rw [← summable_nat_add_iff 1]
    refine hs1.congr fun k => ?_
    simp [QueueData.pPrev]
  have hB' : ∑' k : ℕ, (q.pPrev k : ℝ) * ((k : ℝ) - 1) = q.lam := by
    rw [hBs.tsum_eq_zero_add, hlam]
    simp [QueueData.pPrev]
  have : (fun k : ℕ => w q x k * ((k : ℝ) - 1) ^ 1) =
      fun k => ρ * ((q.p k : ℝ) * ((k : ℝ) - 1)) + (1 - ρ) * ((q.pPrev k : ℝ) * ((k : ℝ) - 1)) := by
    funext k; unfold w; ring
  rw [this, (hA.mul_left ρ).tsum_add (hBs.mul_left (1 - ρ)), tsum_mul_left, tsum_mul_left, hA', hB']
  ring

lemma drift14 (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act) (A : ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ q.n ∧
      P.coeff q.n = A * ((q.n : ℝ) + 1) * (q.lam - q.a x * q.β) ∧
      ∀ i : ℕ, 1 ≤ i →
        Summable (fun j : ℕ => (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1))) ∧
        ∑' j : ℕ, (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1)) = P.eval (i : ℝ) := by
  set N := q.n + 1 with hN
  let T : ℕ → ℝ := fun l => ∑' k : ℕ, w q x k * ((k : ℝ) - 1) ^ (N - l)
  let c : ℕ → ℝ := fun l => A * (N.choose l : ℝ) * T l
  refine ⟨∑ l ∈ Finset.range N, Polynomial.C (c l) * Polynomial.X ^ l, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simp only [Finset.mem_range] at hl; omega
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range N) q.n c, if_pos (by simp [hN])]
    simp only [c, T]
    rw [hN, mu1 q hmom x, Nat.choose_succ_self_right]
    push_cast; ring
  · intro i hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    set G : ℕ → ℝ := fun j => (q.toMDC.P (i' + 1) x j).toReal *
      (A * (j : ℝ) ^ N - A * ((i' + 1 : ℕ) : ℝ) ^ N)
    set y : ℝ := ((i' + 1 : ℕ) : ℝ)
    have hG : ∀ k, G (k + i') = ∑ l ∈ Finset.range N,
        A * (N.choose l : ℝ) * y ^ l * (w q x k * ((k : ℝ) - 1) ^ (N - l)) := by
      intro k
      simp only [G]
      have ht : (q.toMDC.P (i' + 1) x (k + i')).toReal = w q x k := by
        rw [add_comm k i']; exact trans_toReal q x i' k
      rw [ht]
      have hexp : ((k + i' : ℕ) : ℝ) = y + ((k : ℝ) - 1) := by simp [y]; ring
      rw [hexp, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self]
      have hy : ((i' + 1 : ℕ) : ℝ) = y := rfl
      rw [hy]
      simp only [Nat.cast_one, mul_one]
      rw [mul_add, add_sub_cancel_right, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hsl : ∀ l ∈ Finset.range N, Summable fun k : ℕ =>
        A * (N.choose l : ℝ) * y ^ l * (w q x k * ((k : ℝ) - 1) ^ (N - l)) :=
      fun l _ => (summ_wm q hmom x (N - l) (by omega)).mul_left _
    have hsG' : Summable fun k => G (k + i') :=
      (summable_sum hsl).congr fun k => (hG k).symm
    have hsG : Summable G := (summable_nat_add_iff i').1 hsG'
    refine ⟨hsG, ?_⟩
    have hz : ∑ j ∈ Finset.range i', G j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_range] at hj
      simp only [G]
      rw [show q.toMDC.P (i' + 1) x j = q.trans (i' + 1) x j from rfl, trans_low q x i' j hj]
      simp
    show ∑' j, G j = _
    rw [← hsG.sum_add_tsum_nat_add i', hz, zero_add, tsum_congr hG, Summable.tsum_finsetSum hsl,
      Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [tsum_mul_left, Polynomial.eval_C_mul, Polynomial.eval_X_pow]
    simp only [c, T, y]
    ring

end Sennott8D14

open Sennott8D14 in
theorem solution {Act : Type} [Fintype Act] [Nonempty Act] (q : Sennott1989.AvgCost.QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) (x : Act) (A : ℝ) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ q.n ∧
      P.coeff q.n = A * ((q.n : ℝ) + 1) * (q.lam - q.a x * q.β) ∧
      ∀ i : ℕ, 1 ≤ i →
        Summable (fun j : ℕ => (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1))) ∧
        ∑' j : ℕ, (q.toMDC.P i x j).toReal *
          (A * (j : ℝ) ^ (q.n + 1) - A * (i : ℝ) ^ (q.n + 1)) = P.eval (i : ℝ) :=
  drift14 q hmom x A
