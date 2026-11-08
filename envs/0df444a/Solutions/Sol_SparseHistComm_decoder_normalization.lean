-- Prove2me | solution 1 for SparseHistComm.decoder_normalization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:42:47.814532+00:00
-- url     : https://prove2.me/submissions/73fad559-ca55-4a79-80b1-6f8f273b84cc

import Mathlib
import Definitions.Def_SparseHistComm_Admissible
import Definitions.Def_SparseHistComm_empHist
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_clip
import Definitions.Def_SparseHistComm_normalize

namespace Aux_SHC

open SparseHistComm

lemma clip_contract (x h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : |max 0 (min 1 x) - h| ≤ |x - h| := by
  have a1 := neg_abs_le (x - h)
  have a2 := le_abs_self (x - h)
  have a3 := abs_nonneg (x - h)
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx, abs_le]; constructor <;> linarith
  · rcases le_total x 1 with hx1 | hx1
    · rw [min_eq_right hx1, max_eq_right hx]
    · rw [min_eq_left hx1, max_eq_right zero_le_one, abs_le]; constructor <;> linarith

lemma emp_mem {n d : ℕ} (x : Fin n → Finset (Fin d)) (hn : 1 ≤ n) (a : Fin d) :
    0 ≤ empHist x a ∧ empHist x a ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hind : ∀ s : Finset (Fin d), 0 ≤ ind s a ∧ ind s a ≤ 1 := by
    intro s; unfold ind; split_ifs <;> norm_num
  unfold empHist
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hind _).1)
  · have : ∑ i, ind (x i) a ≤ n := by
      calc ∑ i, ind (x i) a ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hind _).2
        _ = n := by simp
    rw [one_div, inv_mul_le_iff₀ hn0]; linarith

lemma emp_sum {n d k : ℕ} (x : Fin n → Finset (Fin d)) (hn : 1 ≤ n) (hx : Admissible k x) :
    ∑ a, empHist x a ≤ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold empHist
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hc : ∀ s : Finset (Fin d), ∑ a, ind s a = s.card := by
    intro s; unfold ind; rw [Finset.sum_ite_mem, Finset.univ_inter]; simp
  simp_rw [hc]
  have : ∑ i, ((x i).card : ℝ) ≤ n * k := by
    calc ∑ i, ((x i).card : ℝ) ≤ ∑ _i : Fin n, (k : ℝ) :=
          Finset.sum_le_sum fun i _ => by exact_mod_cast hx i
      _ = n * k := by simp
  rw [one_div, inv_mul_le_iff₀ hn0]; linarith

end Aux_SHC

open SparseHistComm in
theorem solution (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (v : Fin d → ℝ) :
    (∀ a, 0 ≤ SparseHistComm.normalize k D v a) ∧ ∑ a, |SparseHistComm.normalize k D v a| ≤ k + D ∧
    ∀ x : Fin n → Finset (Fin d), Admissible k x →
      l1 (clip v) (empHist x) ≤ l1 v (empHist x) ∧
      (l1 v (empHist x) ≤ D → l1 (SparseHistComm.normalize k D v) (empHist x) ≤ D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    unfold SparseHistComm.normalize
    split_ifs
    · simp
    · exact le_max_left _ _
  · unfold SparseHistComm.normalize
    split_ifs with h
    · simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · exact not_lt.mp h
  · intro x hx
    have hh := Aux_SHC.emp_mem x hn
    have h3a : l1 (clip v) (empHist x) ≤ l1 v (empHist x) :=
      Finset.sum_le_sum fun a _ => Aux_SHC.clip_contract _ _ (hh a).1 (hh a).2
    refine ⟨h3a, fun hl => ?_⟩
    unfold SparseHistComm.normalize
    split_ifs with h
    · exfalso
      have hb : ∑ a, |clip v a| ≤ l1 (clip v) (empHist x) + ∑ a, empHist x a := by
        unfold l1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro a _
        have := abs_sub_abs_le_abs_sub (clip v a) (empHist x a)
        rw [abs_of_nonneg (hh a).1] at this
        linarith
      linarith [Aux_SHC.emp_sum x hn hx]
    · linarith
