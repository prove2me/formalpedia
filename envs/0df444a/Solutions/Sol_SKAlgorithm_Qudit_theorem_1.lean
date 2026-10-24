-- Prove2me | solution 1 for SKAlgorithm.Qudit.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:23.130051+00:00
-- url     : https://prove2.me/submissions/9488194f-ef7a-4455-afb1-57e066f2c1c8

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model
import Theorems.Thm_SKAlgorithm_Qudit_base_case
import Theorems.Thm_SKAlgorithm_Qudit_eq_33
import Theorems.Thm_SKAlgorithm_Qudit_recursion_invariant
import Theorems.Thm_SKAlgorithm_Qudit_eq_4
import Theorems.Thm_SKAlgorithm_Qudit_eq_7_8

open scoped Matrix
open QAlgorithms SKAlgorithm.Qudit

theorem solution (d : ℕ) (G : Finset (SU d)) (hG : IsInstructionSet G) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ U : SU d,
      ∃ S : List (SU d), (∀ g ∈ S, g ∈ G) ∧
        (S.length : ℝ) ≤ C * Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) ∧
        opDist U (seqUnitary S) < ε := by
  classical
  obtain ⟨c', c'', hc', hc'', hdecomp⟩ := eq_33 d
  obtain ⟨c, εs, hc, hεs, hrec⟩ := recursion_invariant d c' c'' hc' hc''
  let ε₀ := min (εs / 2) (1 / (2 * c ^ 2))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀s : ε₀ ≤ εs := (min_le_left _ _).trans (by linarith)
  have hsmall : ε₀ * c ^ 2 < 1 := by
    have h := (le_div_iff₀ (show 0 < 2 * c ^ 2 by positivity)).mp
      (show ε₀ ≤ 1 / (2 * c ^ 2) from min_le_right _ _)
    nlinarith
  obtain ⟨l₀, hbasicExists⟩ := base_case G hG ε₀ hε₀
  choose basic hbasic using hbasicExists
  have hpos : ∀ n : ℕ, 0 < epsSeq c ε₀ n := by
    intro n
    induction n with
    | zero => exact hε₀
    | succ n ih =>
      rw [show epsSeq c ε₀ (n + 1) = c * epsSeq c ε₀ n ^ ((3 : ℝ) / 2) from
        Function.iterate_succ_apply' _ _ _]
      exact mul_pos hc (Real.rpow_pos_of_pos ih _)
  have hgcExists : ∀ k : ℕ, ∀ Δ : SU d, ∃ VW : SU d × SU d,
      opDist 1 Δ < epsSeq c ε₀ k →
        opDist (VW.1 * VW.2 * VW.1⁻¹ * VW.2⁻¹) Δ <
            c' * epsSeq c ε₀ k ^ ((3 : ℝ) / 2) ∧
          opDist 1 VW.1 < c'' * Real.sqrt (epsSeq c ε₀ k) ∧
          opDist 1 VW.2 < c'' * Real.sqrt (epsSeq c ε₀ k) := by
    intro k Δ
    by_cases hΔ : opDist 1 Δ < epsSeq c ε₀ k
    · obtain ⟨V, W, hVW⟩ := hdecomp (epsSeq c ε₀ k) (hpos k) Δ hΔ
      exact ⟨(V, W), fun _ => hVW⟩
    · exact ⟨(1, 1), fun h => (hΔ h).elim⟩
  choose gc hgc using hgcExists
  have hwords := hrec G hG.1 ε₀ l₀ hε₀ hε₀s basic gc hbasic hgc
  obtain ⟨K, hK, hrate⟩ := eq_7_8 c ε₀ hc hε₀ hsmall
  refine ⟨K * ((l₀ : ℝ) + 1), by positivity, ?_⟩
  intro ε hε U
  obtain ⟨n, hnerr, hnlen⟩ := hrate ε hε
  obtain ⟨hmem, hlen, herr⟩ := hwords n U
  refine ⟨solovayKitaev basic gc n U, hmem, ?_, ?_⟩
  · have hlen' : ((solovayKitaev basic gc n U).length : ℝ) ≤
        (5 : ℝ) ^ n * (l₀ : ℝ) := by exact_mod_cast hlen
    have hp : 0 ≤ Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) := by
      apply Real.rpow_nonneg
      apply Real.log_nonneg
      have h := one_div_pos.mpr hε
      linarith
    calc
      _ ≤ (5 : ℝ) ^ n * (l₀ : ℝ) := hlen'
      _ ≤ (K * Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2))) * (l₀ : ℝ) :=
        mul_le_mul_of_nonneg_right hnlen (Nat.cast_nonneg _)
      _ ≤ K * ((l₀ : ℝ) + 1) *
          Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) := by
        nlinarith [mul_nonneg hK.le hp]
  · rw [eq_4 c ε₀ hc hε₀ n] at herr
    exact herr.trans hnerr
