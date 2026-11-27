-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.lemma_D_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:20.139235+00:00
-- url     : https://prove2.me/submissions/7501af2a-d350-41c7-b93c-17dcc962d637

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (s : Fin n → Fin m → ℝ) (i : Fin n)
    (hvalid : ∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s k j) (j : Fin m) (hv : 0 < I.v i j) :
    StrictConcaveOn ℝ (Set.Ici 0)
        (fun t : ℝ => 1 / I.v i j * (t / (t + ∑ k ∈ Finset.univ.erase i, s k j))) ∧
      ConcaveOn ℝ (orthant m)
        (fun si : Fin m → ℝ =>
          1 / I.v i j * (si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j))) := by
            let c : ℝ := ∑ k ∈ Finset.univ.erase i, s k j
            let A : ℝ := 1 / I.v i j
            have hc : 0 < c := hvalid j
            have hA : 0 < A := one_div_pos.mpr hv
            have hslope : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u < v →
                (A * (v / (v + c)) - A * (u / (u + c))) / (v - u) =
                  A * c / ((u + c) * (v + c)) := by
              intro u v hu hv huv
              have hu' : u + c ≠ 0 := ne_of_gt (by linarith)
              have hv' : v + c ≠ 0 := ne_of_gt (by linarith)
              have huv' : v - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
              field_simp
              ring
            have hstrict : StrictConcaveOn ℝ (Set.Ici 0)
                (fun t : ℝ => A * (t / (t + c))) := by
              apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ici (0 : ℝ))
              intro x y z hx hz hxy hyz
              have hx0 : 0 ≤ x := hx
              have hz0 : 0 ≤ z := hz
              have hy0 : 0 ≤ y := le_trans hx0 hxy.le
              rw [hslope y z hy0 hz0 hyz, hslope x y hx0 hy0 hxy]
              have hxc : 0 < x + c := by linarith
              have hyc : 0 < y + c := by linarith
              have hzc : 0 < z + c := by linarith
              apply (div_lt_div_iff₀ (mul_pos hyc hzc) (mul_pos hxc hyc)).mpr
              nlinarith [mul_pos hA hc,
                mul_pos (mul_pos hA hc) (mul_pos hyc (sub_pos.mpr (lt_trans hxy hyz)))]
            refine ⟨hstrict, ?_⟩
            refine ⟨?_, ?_⟩
            · intro x hx y hy a b ha hb hab k
              exact add_nonneg (mul_nonneg ha (hx k)) (mul_nonneg hb (hy k))
            · intro x hx y hy a b ha hb hab
              exact hstrict.concaveOn.2 (hx j) (hy j) ha hb hab
