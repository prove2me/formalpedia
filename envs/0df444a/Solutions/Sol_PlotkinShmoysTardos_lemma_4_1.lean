-- Prove2me | solution 1 for PlotkinShmoysTardos.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:22.214797+00:00
-- url     : https://prove2.me/submissions/4108a228-67bd-46f8-98c9-2b5b2177c741

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality

open Finset Matrix PlotkinShmoysTardos

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (x : Fin n → ℝ) (hx : x ∈ P) (l : ℝ)
    (hfeas : ∀ i, A.mulVec x i ≤ b i + l * d i) (y : Fin m → ℝ) (hy : 0 ≤ y) (hy0 : y ≠ 0)
    (hG1 : G1 A b d x l y) (hG2 : G2 A b d P x l y) (hl : 0 < l) :
    ¬ ∃ z, IsExact A b P z := by
  let _ := hx
  let _ := hfeas
  rintro ⟨z, hzP, hz_le⟩
  have hex_i : ∃ i : Fin m, y i ≠ 0 := Function.ne_iff.mp hy0
  rcases hex_i with ⟨i₀, hi₀_ne⟩
  have hy_pos : 0 < y i₀ := lt_of_le_of_ne (hy i₀) (Ne.symm hi₀_ne)
  have hyd_pos : 0 < y ⬝ᵥ d := by
    simp only [dotProduct]
    exact sum_pos' (fun i _ => mul_nonneg (hy i) (le_of_lt (hd i)))
      ⟨i₀, mem_univ i₀, mul_pos hy_pos (hd i₀)⟩
  have hz_nonpos : y ⬝ᵥ (A.mulVec z - b) ≤ 0 := by
    simp only [dotProduct, Pi.sub_apply]
    exact sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy i) (sub_nonpos.mpr (hz_le i))
  have h1 : l * (y ⬝ᵥ d) ≤ 4 * (y ⬝ᵥ (A.mulVec x - b)) := hG1
  have h2 : y ⬝ᵥ (A.mulVec x - b) - y ⬝ᵥ (A.mulVec z - b) ≤ l / 5 * (y ⬝ᵥ d) := hG2 z hzP
  have hprod_pos : 0 < l * (y ⬝ᵥ d) := mul_pos hl hyd_pos
  linarith
