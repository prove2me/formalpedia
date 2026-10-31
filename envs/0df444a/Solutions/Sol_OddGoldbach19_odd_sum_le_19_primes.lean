-- Prove2me | solution 1 for OddGoldbach19.odd_sum_le_19_primes
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:55:28.622+00:00
-- url     : https://prove2.me/submissions/1269553f-f531-40ef-b432-347a37a1c4ed

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_OddGoldbach19_small_density_A
import Theorems.Thm_Schnir_basis_of_density
import Theorems.Thm_OddGoldbach19_medium_count_log260
import Theorems.Thm_OddGoldbach19_large_count_exp260
set_option autoImplicit false
open Schnir Finset Real Classical
namespace OddGoldbach19
theorem s6d_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p≠2) : p%2=1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two h2)
open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem s6d_large (N : ℕ) :
    #((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by
  set T := (range (2 * N + 6 + 1)).filter (fun s => 0 < r s) with hT
  have hmem : ∀ s ∈ T, ∃ p q, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ s = p + q ∧ s ≤ 2 * N + 6 := by
    intro s hs
    simp only [hT, mem_filter, mem_range] at hs
    obtain ⟨hs1, hs2⟩ := hs
    unfold r at hs2
    obtain ⟨p, hp⟩ := card_pos.1 hs2
    simp only [mem_filter, mem_range] at hp
    exact ⟨p, s - p, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by omega, by omega⟩
  have hinj : Set.InjOn (fun s => (s - 6) / 2) (T : Set ℕ) := by
    intro s hs t ht hst
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, -⟩ := hmem s hs
    obtain ⟨p', q', hp', hp2', hq', hq2', rfl, -⟩ := hmem t ht
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := s6d_odd_of_prime hp' hp2'
    have := s6d_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := hp.two_le; have := hq.two_le
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h0 : (p + q - 6) / 2 = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      have : (p + q - 6) / 2 = (p - 3) / 2 + (q - 3) / 2 := by omega
      rw [this]
      open Pointwise in
      exact Set.mem_add.2 ⟨(p - 3) / 2, ⟨p, hp, hp2, rfl⟩, (q - 3) / 2, ⟨q, hq, hq2, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)


open Classical in
theorem density_from_count
    (hcount : ∀ n : ℕ, 26≤log (n:ℝ) →
      (n:ℝ)*(100/1799:ℝ)≤(((range (n+1)).filter (fun s=>0<r s)).card:ℝ)) :
    (1:ℝ)/9≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0:ℝ)<N := by exact_mod_cast hN
  apply (le_div_iff₀ hNpos).mpr
  by_cases hl : log ((2*N+6:ℕ):ℝ)≤26
  · have hs := small_density_A N (by omega) hl
    nlinarith
  · have hl' : 26≤log ((2*N+6:ℕ):ℝ) := (lt_of_not_ge hl).le
    have hnpos : (0:ℝ)<((2*N+6:ℕ):ℝ) := by positivity
    have he : exp 26≤((2*N+6:ℕ):ℝ) := (le_log_iff_exp_le hnpos).mp hl'
    have hex : (40006:ℝ)≤exp 26 := by
      have he1 : (2:ℝ)≤exp 1 := by linarith [exp_one_gt_d9]
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) he1 26
      have heq : exp 26=exp 1^26 := by rw [←exp_nat_mul];norm_num
      rw [heq]
      norm_num at hp ⊢
      linarith
    have hNR : (20000:ℝ)≤N := by push_cast at he;linarith
    have hr := hcount (2*N+6) hl'
    have hc : (((range (2*N+6+1)).filter (fun s=>0<r s)).card:ℝ)≤
        (((Ioc 0 N).filter (fun a=>a∈A)).card:ℝ)+1 := by exact_mod_cast s6d_large N
    push_cast at hr
    nlinarith
open Pointwise

theorem s6m_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def s6m_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem s6m_P_add {j k t u : ℕ} (h1 : s6m_P j t) (h2 : s6m_P k u) : s6m_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem s6m_P_B {b : ℕ} (hb : b ∈ B) : s6m_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem s6m_P_A {a : ℕ} (ha : a ∈ A) : s6m_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact s6m_P_add (s6m_P_B hb) (s6m_P_B hc)


theorem n9_P_multiset (t : Multiset ℕ) (ht : ∀ x ∈ t, x ∈ A) : s6m_P (2 * t.card) t.sum := by
  induction t using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | cons a t ih =>
    have h1 := ih (fun x hx => ht x (Multiset.mem_cons_of_mem hx))
    have h2 := s6m_P_A (ht a (Multiset.mem_cons_self a t))
    have := s6m_P_add h2 h1
    rw [Multiset.card_cons, Multiset.sum_cons]
    rwa [show 2 * (t.card + 1) = 2 + 2 * t.card by ring]

open Classical in
theorem n9_all (hA : (1:ℝ)/9≤ schnirelmannDensity A) (t : ℕ) : s6m_P 18 t := by
  have hk : (1 : ℝ) ≤ ((9 : ℕ) : ℝ) * schnirelmannDensity A := by
    push_cast; linarith
  obtain ⟨u, hu1, hu2, hu3⟩ := basis_of_density A s6m_zero_mem_A 9 hk t
  have := n9_P_multiset u hu2
  rwa [hu1, hu3] at this

/-- Every odd n≥39 is a sum of exactly19 primes, given the density input. -/
theorem exact_19 (hA : (1:ℝ)/9≤ schnirelmannDensity A) (n : ℕ) (hodd : Odd n) (hn : 39 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 19 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 57 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := n9_all hA ((n - 57) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 38) 3 + Multiset.replicate (57 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega


theorem endpoint_from_density (hA : (1:ℝ)/9≤ schnirelmannDensity A)
    (n : ℕ) (hodd : Odd n) (hn : 1<n) :
    ∃ s : Multiset ℕ, s.card≤19 ∧ (∀p∈s,Nat.Prime p) ∧ s.sum=n := by
  by_cases hbig : 39≤n
  · obtain ⟨s,hs1,hs2,hs3⟩ := exact_19 hA n hodd hbig
    exact ⟨s,hs1.le,hs2,hs3⟩
  · have hn2 := Nat.odd_iff.mp hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n-3)/2) 2,by simp;omega,fun p hp=>?_,?_⟩
    · rcases Multiset.mem_cons.mp hp with h|h
      · rw [h];exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h];exact Nat.prime_two
    · simp;omega
end OddGoldbach19
#print axioms OddGoldbach19.density_from_count
#print axioms OddGoldbach19.endpoint_from_density
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 19 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n  := by
  apply OddGoldbach19.endpoint_from_density _ n hodd hn
  apply OddGoldbach19.density_from_count
  intro m hm
  by_cases h260 : Real.log (m:ℝ)≤260
  · exact OddGoldbach19.medium_count_log260 m hm h260
  · have hmN : 0 < m := by
      by_contra hh
      have hz : m=0 := by omega
      subst m
      norm_num at hm
    have hmR : (0:ℝ) < m := by exact_mod_cast hmN
    exact OddGoldbach19.large_count_exp260 m
      ((Real.le_log_iff_exp_le hmR).mp (by linarith))
#print axioms solution
