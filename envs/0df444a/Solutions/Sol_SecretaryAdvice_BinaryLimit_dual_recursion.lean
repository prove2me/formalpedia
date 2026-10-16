-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.dual_recursion
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:28:00.400034+00:00
-- url     : https://prove2.me/submissions/b1ecb914-d2fa-49da-9843-446fd63a3ea3

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
set_option autoImplicit false
open SecretaryAdvice.BinaryLimit
namespace SecretaryResearch

theorem stable (n : ℕ) (p pp : ℝ) (a b i : ℕ) (s : Bool) (hab : a ≤ b)
    (hi : n-a < i) : greedyStages n p pp b i s = greedyStages n p pp a i s := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    simp only [greedyStages,if_neg (show i ≠ n-b by omega)]
    exact ih

theorem recurrence (n : ℕ) (p pp : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    w n p pp i s = max 0 ((if s then p else 1-p) -
      (if s then 1-pp else pp)/(i : ℝ) *
        ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)) := by
  have hbase : n-(n-i)=i := by omega
  rw [w, stable n p pp (n-i+1) n i s (by omega) (by omega)]
  simp only [greedyStages,hbase,↓reduceIte]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ioc.mp hj
  congr 1 <;> symm <;> exact stable n p pp (n-i) n j _ (by omega) (by omega)

theorem nonneg (n : ℕ) (p pp : ℝ) (k i : ℕ) (s : Bool) :
    0 ≤ greedyStages n p pp k i s := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · exact le_max_left _ _
    · exact ih

theorem coord_mono (n : ℕ) (p pp : ℝ) (hpp0 : 0 ≤ pp) (hpp1 : pp ≤ 1)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) (s : Bool) :
    w n p pp i s ≤ w n p pp j s := by
  rw [recurrence n p pp i hi (hij.trans hjn) s,recurrence n p pp j (hi.trans hij) hjn s]
  apply max_le_max_left
  have ha : 0 ≤ (if s then 1-pp else pp) := by split <;> linarith
  have hFi : 0 ≤ ∑ k ∈ Finset.Ioc i n, (w n p pp k true + w n p pp k false) :=
    Finset.sum_nonneg (fun k _ => add_nonneg (nonneg ..) (nonneg ..))
  have hFj : 0 ≤ ∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false) :=
    Finset.sum_nonneg (fun k _ => add_nonneg (nonneg ..) (nonneg ..))
  have hF : (∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false)) ≤
      ∑ k ∈ Finset.Ioc i n, (w n p pp k true + w n p pp k false) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Ioc] at *
      omega
    · intro k _ _
      exact add_nonneg (nonneg ..) (nonneg ..)
  have hden : (if s then 1-pp else pp)/(j : ℝ) ≤ (if s then 1-pp else pp)/(i : ℝ) :=
    div_le_div_of_nonneg_left ha (by exact_mod_cast hi) (by exact_mod_cast hij)
  exact sub_le_sub_left (mul_le_mul hden hF hFj (div_nonneg ha (Nat.cast_nonneg i))) _

end SecretaryResearch
#print axioms SecretaryResearch.recurrence
#print axioms SecretaryResearch.coord_mono

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dütting, Lattanzi, Paes Leme and Vassilvitskii, arXiv:2011.06726v1, early Y recursion.
theorem solution (n : ℕ) (p pp : ℝ) (_hn : 1 ≤ n)
    (_hp0 : (1/2 : ℝ) ≤ p) (_hp1 : p ≤ 1)
    (hpp0 : (1/2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1)
    (i : ℕ) (hi0 : 1 ≤ i) (hY : tY n p pp ≤ i) (hN : i+1 < tN n p pp) :
    w n p pp i true = ((i : ℝ)+pp)/(i : ℝ)*w n p pp (i+1) true-p/(i : ℝ) := by
  classical
  have hNupper : tN n p pp ≤ n+1 := by
    unfold tN
    split_ifs with h
    · obtain ⟨j,hj,hjn,hp⟩ := h
      have hle : sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k false} ≤ j :=
        Nat.sInf_le ⟨hj,hjn,hp⟩
      omega
    · exact le_rfl
  have hin : i+1 ≤ n := by omega
  have hpos (j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : 0 < w n p pp j true := by
    have hyex : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k true := by
      by_contra h
      simp only [tY,if_neg h] at hY
      omega
    have hmem := Nat.sInf_mem hyex
    have hqle : sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k true} ≤ j := by
      simpa only [tY,if_pos hyex] using hY.trans hij
    exact hmem.2.2.trans_le (SecretaryResearch.coord_mono n p pp (by linarith) hpp1
      _ j hmem.1 hqle hjn true)
  have hNzero : w n p pp (i+1) false = 0 := by
    apply le_antisymm _ (SecretaryResearch.nonneg ..)
    by_contra h
    have hp : 0 < w n p pp (i+1) false := lt_of_not_ge h
    have he : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k false := ⟨i+1,by omega,hin,hp⟩
    have hl : tN n p pp ≤ i+1 := by
      simp only [tN,if_pos he]
      exact Nat.sInf_le ⟨by omega,hin,hp⟩
    omega
  have hwi := SecretaryResearch.recurrence n p pp i hi0 (by omega) true
  have hwj := SecretaryResearch.recurrence n p pp (i+1) (by omega) hin true
  simp only [if_true] at hwi hwj
  have hwi' : w n p pp i true = p - (1-pp)/(i : ℝ)*
      ∑ j ∈ Finset.Ioc i n, (w n p pp j true+w n p pp j false) := by
    have hp := hpos i le_rfl (by omega)
    rw [hwi] at hp
    have hraw := (lt_max_iff.mp hp).resolve_left (lt_irrefl (0 : ℝ))
    exact hwi.trans (max_eq_right hraw.le)
  have hwj' : w n p pp (i+1) true = p - (1-pp)/((i+1 : ℕ) : ℝ)*
      ∑ j ∈ Finset.Ioc (i+1) n, (w n p pp j true+w n p pp j false) := by
    have hp := hpos (i+1) (by omega) hin
    rw [hwj] at hp
    have hraw := (lt_max_iff.mp hp).resolve_left (lt_irrefl (0 : ℝ))
    exact hwj.trans (max_eq_right hraw.le)
  have hsplit : (∑ j ∈ Finset.Ioc i n, (w n p pp j true+w n p pp j false)) =
      w n p pp (i+1) true + ∑ j ∈ Finset.Ioc (i+1) n, (w n p pp j true+w n p pp j false) := by
    have hset : Finset.Ioc i n = insert (i+1) (Finset.Ioc (i+1) n) := by
      ext j
      simp only [Finset.mem_Ioc,Finset.mem_insert]
      omega
    rw [hset,Finset.sum_insert (by simp),hNzero,add_zero]
  rw [hsplit] at hwi'
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  have hjR : (i : ℝ)+1 ≠ 0 := by positivity
  push_cast at hwj'
  field_simp [hiR,hjR] at hwi' hwj' ⊢
  nlinarith only [hwi',hwj']

#print axioms solution
