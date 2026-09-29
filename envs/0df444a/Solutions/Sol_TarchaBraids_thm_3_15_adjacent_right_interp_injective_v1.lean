-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_right_interp_injective_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T11:04:05.503861+00:00
-- url     : https://prove2.me/submissions/467761b7-db91-4f32-9b55-0a7e033e6359

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_pairwise_separation_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_outside_separation_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightOuterInterpFun_outside_injective_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ) (k : Fin n)
    (h0 : (k : ℕ) ≠ (i : ℕ)) (h1 : (k : ℕ) ≠ (i : ℕ) + 1)
    (h2 : (k : ℕ) ≠ (i : ℕ) + 2) :
    rightOuterInterpFun n i j u q k = (((k : ℕ) + 1 : ℝ) : ℂ) := by
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [rightOuterInterpFun, hO.right_outside q k h0 h1 h2,
    hO.outer_outside q k h0 h1 h2]
  unfold braidInterp
  module

lemma rightOuterInterpFun_injective_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Function.Injective (rightOuterInterpFun n i j u q) := by
  have hp := thm_3_15_adjacent_right_pairwise_separation_v1 i j hji
  have ho := thm_3_15_adjacent_right_outside_separation_v1 i j hji
  intro k l hkl
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · have hk : k = strandIdx i := by
      apply Fin.ext
      simpa [strandIdx] using hk0
    subst k
    by_cases hl0 : (l : ℕ) = (i : ℕ)
    · apply Fin.ext
      simpa [strandIdx] using hl0.symm
    · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
      · have hl : l = strandIdxSucc i := by
          apply Fin.ext
          simpa [strandIdxSucc] using hl1
        subst l
        exact absurd hkl (hp.1 u q hu0 hu1 hq0 hq1)
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
        · have hl : l = strandIdxSucc j := by
            apply Fin.ext
            simpa [strandIdxSucc, hji] using hl2
          subst l
          exact absurd hkl (hp.2.1 u q hu0 hu1 hq0 hq1)
        · exact absurd hkl (ho.1 u q hu0 hu1 l hl0 hl1 hl2)
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · have hk : k = strandIdxSucc i := by
        apply Fin.ext
        simpa [strandIdxSucc] using hk1
      subst k
      by_cases hl0 : (l : ℕ) = (i : ℕ)
      · have hl : l = strandIdx i := by
          apply Fin.ext
          simpa [strandIdx] using hl0
        subst l
        exact absurd hkl.symm (hp.1 u q hu0 hu1 hq0 hq1)
      · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
        · apply Fin.ext
          simpa [strandIdxSucc] using hl1.symm
        · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
          · have hl : l = strandIdxSucc j := by
              apply Fin.ext
              simpa [strandIdxSucc, hji] using hl2
            subst l
            exact absurd hkl (hp.2.2 u q hu0 hu1 hq0 hq1)
          · exact absurd hkl (ho.2.1 u q hu0 hu1 l hl0 hl1 hl2)
    · by_cases hk2 : (k : ℕ) = (i : ℕ) + 2
      · have hk : k = strandIdxSucc j := by
          apply Fin.ext
          simpa [strandIdxSucc, hji] using hk2
        subst k
        by_cases hl0 : (l : ℕ) = (i : ℕ)
        · have hl : l = strandIdx i := by
            apply Fin.ext
            simpa [strandIdx] using hl0
          subst l
          exact absurd hkl.symm (hp.2.1 u q hu0 hu1 hq0 hq1)
        · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
          · have hl : l = strandIdxSucc i := by
              apply Fin.ext
              simpa [strandIdxSucc] using hl1
            subst l
            exact absurd hkl.symm (hp.2.2 u q hu0 hu1 hq0 hq1)
          · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
            · apply Fin.ext
              simpa [strandIdxSucc, hji] using hl2.symm
            · exact absurd hkl (ho.2.2 u q hu0 hu1 l hl0 hl1 hl2)
      · by_cases hl0 : (l : ℕ) = (i : ℕ)
        · have hl : l = strandIdx i := by
            apply Fin.ext
            simpa [strandIdx] using hl0
          subst l
          exact absurd hkl.symm (ho.1 u q hu0 hu1 k hk0 hk1 hk2)
        · by_cases hl1 : (l : ℕ) = (i : ℕ) + 1
          · have hl : l = strandIdxSucc i := by
              apply Fin.ext
              simpa [strandIdxSucc] using hl1
            subst l
            exact absurd hkl.symm (ho.2.1 u q hu0 hu1 k hk0 hk1 hk2)
          · by_cases hl2 : (l : ℕ) = (i : ℕ) + 2
            · have hl : l = strandIdxSucc j := by
                apply Fin.ext
                simpa [strandIdxSucc, hji] using hl2
              subst l
              exact absurd hkl.symm (ho.2.2 u q hu0 hu1 k hk0 hk1 hk2)
            · rw [rightOuterInterpFun_outside_injective_v1 i j hji u q k hk0 hk1 hk2,
                rightOuterInterpFun_outside_injective_v1 i j hji u q l hl0 hl1 hl2] at hkl
              have hre : ((k : ℕ) : ℝ) = (l : ℕ) := by
                simpa using congrArg Complex.re hkl
              apply Fin.ext
              exact_mod_cast hre

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
      Function.Injective (rightOuterInterpFun n i j u q) := by
  intro n i j hji u q hu0 hu1 hq0 hq1
  exact rightOuterInterpFun_injective_v1 i j hji u q hu0 hu1 hq0 hq1
