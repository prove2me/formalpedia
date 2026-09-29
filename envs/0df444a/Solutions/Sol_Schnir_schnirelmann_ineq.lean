-- Prove2me | solution 1 for Schnir.schnirelmann_ineq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:59:53.691174+00:00
-- url     : https://prove2.me/submissions/73aa5e71-7adf-41bf-a9cc-ebc91fa3f9c9

import Mathlib
import Definitions.Def_Schnir_defs

open Finset Real

namespace Schnir

open Pointwise Classical in
/-- Key counting bound for Schnirelmann's inequality (gap argument, by strong induction). -/
theorem schnirAdd_count (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) (N : ℕ) :
    (#{a ∈ Ioc 0 N | a ∈ D} : ℝ) + schnirelmannDensity E * ((N : ℝ) - #{a ∈ Ioc 0 N | a ∈ D})
      ≤ #{a ∈ Ioc 0 N | a ∈ D + E} := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  by_cases hND : N ∈ D
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hI : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
      ext x; simp only [mem_insert, mem_Ioc]; omega
    have hnm : n + 1 ∉ Ioc 0 n := by simp
    have hNDE : n + 1 ∈ D + E := Set.mem_add.2 ⟨n + 1, hND, 0, hE, rfl⟩
    have h1 : #{a ∈ Ioc 0 (n + 1) | a ∈ D} = #{a ∈ Ioc 0 n | a ∈ D} + 1 := by
      rw [hI, filter_insert, if_pos hND, card_insert_of_notMem (by simp)]
    have h2 : #{a ∈ Ioc 0 (n + 1) | a ∈ D + E} = #{a ∈ Ioc 0 n | a ∈ D + E} + 1 := by
      rw [hI, filter_insert, if_pos hNDE, card_insert_of_notMem (by simp)]
    have := ih n (by omega)
    rw [h1, h2]; push_cast at this ⊢; linarith
  · set d := Nat.findGreatest (· ∈ D) N with hd
    have hdD : d ∈ D := Nat.findGreatest_spec (P := (· ∈ D)) (Nat.zero_le N) hD
    have hdN : d ≤ N := Nat.findGreatest_le N
    have hdlt : d < N := lt_of_le_of_ne hdN (fun h => hND (h ▸ hdD))
    have hgr : ∀ k, d < k → k ≤ N → k ∉ D := fun k h1 h2 =>
      Nat.findGreatest_is_greatest (P := (· ∈ D)) h1 h2
    have hk : #{a ∈ Ioc 0 N | a ∈ D} = #{a ∈ Ioc 0 d | a ∈ D} := by
      congr 1; ext a; simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        by_contra h; exact hgr a (by omega) h2 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
    set S2 := ({e ∈ Ioc 0 (N - d) | e ∈ E}).image (fun e => d + e) with hS2
    have hS2c : #S2 = #{e ∈ Ioc 0 (N - d) | e ∈ E} :=
      card_image_of_injective _ (fun x y h => by simpa using h)
    have hdisj : Disjoint {a ∈ Ioc 0 d | a ∈ D + E} S2 := by
      rw [disjoint_left]
      intro a ha hb
      simp only [hS2, mem_image, mem_filter, mem_Ioc] at ha hb
      obtain ⟨e, ⟨⟨he1, _⟩, _⟩, rfl⟩ := hb
      omega
    have hsub : {a ∈ Ioc 0 d | a ∈ D + E} ∪ S2 ⊆ {a ∈ Ioc 0 N | a ∈ D + E} := by
      intro a ha
      rcases mem_union.1 ha with ha | ha
      · simp only [mem_filter, mem_Ioc] at ha ⊢; exact ⟨⟨ha.1.1, by omega⟩, ha.2⟩
      · simp only [hS2, mem_image, mem_filter, mem_Ioc] at ha
        obtain ⟨e, ⟨⟨he1, he2⟩, he⟩, rfl⟩ := ha
        simp only [mem_filter, mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, Set.mem_add.2 ⟨d, hdD, e, he, rfl⟩⟩
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj, hS2c] at hcard
    have hE' : schnirelmannDensity E * ((N - d : ℕ) : ℝ) ≤ #{e ∈ Ioc 0 (N - d) | e ∈ E} :=
      schnirelmannDensity_mul_le_card_filter
    have hih := ih d hdlt
    rw [Nat.cast_sub hdN] at hE'
    rw [hk]
    have hcard' : ((#{a ∈ Ioc 0 d | a ∈ D + E} : ℕ) : ℝ) + #{e ∈ Ioc 0 (N - d) | e ∈ E}
        ≤ #{a ∈ Ioc 0 N | a ∈ D + E} := by exact_mod_cast hcard
    nlinarith

open Pointwise Classical in
/-- Note eq. (17): Schnirelmann's inequality `σ(D+E) ≥ σ(D) + σ(E) - σ(D)σ(E)` when `0 ∈ D ∩ E`. -/
theorem schnirelmann_ineq (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    schnirelmannDensity D + schnirelmannDensity E
      - schnirelmannDensity D * schnirelmannDensity E ≤ schnirelmannDensity (D + E) := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos]
  have h1 := schnirAdd_count D E hD hE N
  have h2 : schnirelmannDensity D * N ≤ #{a ∈ Ioc 0 N | a ∈ D} :=
    schnirelmannDensity_mul_le_card_filter
  have h3 : schnirelmannDensity E ≤ 1 := schnirelmannDensity_le_one
  have h4 : 0 ≤ schnirelmannDensity E := schnirelmannDensity_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 h3)]

end Schnir

open Pointwise Classical in
open Schnir in
theorem solution (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    schnirelmannDensity D + schnirelmannDensity E
      - schnirelmannDensity D * schnirelmannDensity E ≤ schnirelmannDensity (D + E) :=
  Schnir.schnirelmann_ineq D E hD hE
