-- Prove2me | solution 1 for Schnir.density_A
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:59:52.671983+00:00
-- url     : https://prove2.me/submissions/0239a88d-4a58-42fd-bdda-5a7412c71fb8

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_R_lower
import Theorems.Thm_Schnir_pi_lower

open Finset Real

namespace Schnir

theorem dens_zero_mem_B : 0 ∈ B := ⟨3, Nat.prime_three, by norm_num, rfl⟩

theorem dens_B_sub_A : B ⊆ A := by
  intro b hb
  open Pointwise in exact Set.mem_add.2 ⟨0, dens_zero_mem_B, b, hb, zero_add b⟩

theorem dens_one_mem_A : 1 ∈ A :=
  dens_B_sub_A ⟨5, by norm_num, by norm_num, rfl⟩

theorem dens_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

open Classical in
/-- Medium range: `#(A ∩ [1,N]) + 2 ≥ π(2N+3)`. -/
theorem dens_medium (N : ℕ) :
    Nat.primeCounting (2 * N + 3) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
  set T := (range (2 * N + 4)).filter (fun p => p.Prime ∧ 5 ≤ p) with hT
  have h1 : Nat.primeCounting (2 * N + 3) ≤ #T + 2 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (2 * N + 3 + 1)).filter Nat.Prime ⊆ insert 2 (insert 3 T) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_insert, hT, mem_filter, mem_range]
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨by omega, hp.2, h5⟩)
      · have := hp.2.two_le
        interval_cases p
        · simp
        · simp
        · exact absurd hp.2 (by norm_num)
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans ?_
    have := card_insert_le 3 T
    omega
  have h2 : #T ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
    have hinj : Set.InjOn (fun p => (p - 3) / 2) (T : Set ℕ) := by
      intro p hp q hq hpq
      simp only [hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hp hq
      have := dens_odd_of_prime hp.2.1 (by omega)
      have := dens_odd_of_prime hq.2.1 (by omega)
      simp only at hpq
      omega
    rw [← card_image_of_injOn hinj]
    apply card_le_card
    intro a ha
    simp only [hT, mem_image, mem_filter, mem_range] at ha
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩ := ha
    have := dens_odd_of_prime hp2 (by omega)
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, dens_B_sub_A ⟨p, hp2, by omega, rfl⟩⟩
  omega

open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem dens_large (N : ℕ) :
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
    have := dens_odd_of_prime hp hp2
    have := dens_odd_of_prime hq hq2
    have := dens_odd_of_prime hp' hp2'
    have := dens_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := dens_odd_of_prime hp hp2
    have := dens_odd_of_prime hq hq2
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
/-- Note eq. (16): `σ(A) ≥ 1/35000`. -/
theorem density_A : (1 : ℝ) / 35000 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 35000
  · have h1 : 1 ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
      apply card_pos.2
      exact ⟨1, by simp only [mem_filter, mem_Ioc]; exact ⟨⟨by norm_num, hN⟩, dens_one_mem_A⟩⟩
    have : (1 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by exact_mod_cast h1
    have : (N : ℝ) ≤ 35000 := by exact_mod_cast hsmall
    linarith
  push Not at hsmall
  have hN' : (35001 : ℝ) ≤ N := by exact_mod_cast hsmall
  by_cases hbig : Real.exp 2000 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := R_lower _ hbig
    rw [Nat.floor_natCast] at hR
    have hL := dens_large N
    have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
        ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
    -- lower bound on N
    have hexp : (501 : ℝ) ^ 4 ≤ Real.exp 2000 := by
      have : Real.exp 2000 = Real.exp 500 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : (501 : ℝ) ≤ Real.exp 500 := by
        have := Real.add_one_le_exp (500 : ℝ); linarith
      gcongr
    push_cast at hR hbig
    nlinarith
  · push Not at hbig
    have hy : (1000 : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hP := pi_lower _ hy
    rw [Nat.floor_natCast] at hP
    have hM := dens_medium N
    have hM' : (Nat.primeCounting (2 * N + 3) : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
      exact_mod_cast hM
    have hypos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by linarith
    have hlog : Real.log ((2 * N + 3 : ℕ) : ℝ) < 2000 := by
      rw [Real.log_lt_iff_lt_exp hypos]
      push_cast at hbig ⊢; linarith
    have hlogpos : 0 < Real.log ((2 * N + 3 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hfrac : 2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * 2000) ≤
        2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * Real.log ((2 * N + 3 : ℕ) : ℝ)) := by
      gcongr
    push_cast at hfrac hP
    nlinarith
    
end Schnir

open Classical in
open Schnir in
theorem solution : (1 : ℝ) / 35000 ≤ schnirelmannDensity A :=
  Schnir.density_A
