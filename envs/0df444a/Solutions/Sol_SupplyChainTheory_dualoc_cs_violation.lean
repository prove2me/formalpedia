-- Prove2me | solution 1 for SupplyChainTheory.dualoc_cs_violation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:31.084189+00:00
-- url     : https://prove2.me/submissions/8e311727-cc08-40a5-891d-e89bfccce207

import Mathlib
import Definitions.Def_SupplyChainTheory_location

open SupplyChainTheory


theorem solution {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a)
    (i : Fin n) :
    ViolatesCS chat v Jp a i ↔ 2 ≤ (Jp.filter (fun j => chat i j < v i)).card := by
  classical
  have hnear : chat i (a i) ≤ v i := by
    obtain ⟨j, hj, hjv⟩ := hPDP.2 i
    exact ((ha i).2 j hj).trans hjv
  -- A violation is an open site other than `j⁺(i)` strictly within `vᵢ`.
  have hviol : ViolatesCS chat v Jp a i ↔ ∃ j ∈ Jp, j ≠ a i ∧ chat i j < v i := by
    constructor
    · rintro ⟨j, hj⟩
      have hja : j ≠ a i := by
        rintro rfl; apply hj; simp [primalY, primalX, (ha i).1]
      have hjJ : j ∈ Jp := by
        by_contra hjJ; apply hj; simp [primalY, primalX, hja, hjJ]
      refine ⟨j, hjJ, hja, ?_⟩
      by_contra hle; push Not at hle
      apply hj; rw [max_eq_left (by linarith), zero_mul]
    · rintro ⟨j, hjJ, hja, hlt⟩
      refine ⟨j, ?_⟩
      simp only [primalY, primalX, if_neg hja, if_pos hjJ, max_eq_right (by linarith : 0 ≤ v i - chat i j)]
      intro h0
      have : v i - chat i j = 0 := by linarith
      linarith
  rw [hviol]
  constructor
  · rintro ⟨j, hjJ, hja, hlt⟩
    have h1 : 1 < (Jp.filter (fun j => chat i j < v i)).card := by
      rw [Finset.one_lt_card]
      refine ⟨j, Finset.mem_filter.mpr ⟨hjJ, hlt⟩, a i, Finset.mem_filter.mpr ⟨(ha i).1, ?_⟩, hja⟩
      exact lt_of_le_of_lt ((ha i).2 j hjJ) hlt
    omega
  · intro h2
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Jp.filter (fun j => chat i j < v i)).card)
    rw [Finset.mem_filter] at hj₁ hj₂
    by_cases h1 : j₁ = a i
    · exact ⟨j₂, hj₂.1, fun h => hne (h1.trans h.symm), hj₂.2⟩
    · exact ⟨j₁, hj₁.1, h1, hj₁.2⟩
