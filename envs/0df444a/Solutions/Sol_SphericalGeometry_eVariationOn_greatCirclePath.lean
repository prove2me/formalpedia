-- Prove2me | solution 1 for SphericalGeometry.eVariationOn_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:34:26.461273+00:00
-- url     : https://prove2.me/submissions/f3a00307-b8cd-4cc8-b230-f546fade85a8

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_dist_greatCirclePath
import Theorems.Thm_SphericalGeometry_lipschitzWith_greatCirclePath
import Theorems.Thm_MeasureTheory_eVariationOn_le_of_lipschitzOnWith

open SphericalGeometry Filter

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (greatCirclePath v1 v2) (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  set gamma : ℝ → E := greatCirclePath v1 v2 with hgdef
  have hlip : LipschitzWith 1 gamma :=
    SphericalGeometry.lipschitzWith_greatCirclePath v1 v2 h1 h2 ho
  refine le_antisymm ?_ ?_
  · have h := MeasureTheory.eVariationOn_le_of_lipschitzOnWith gamma 1 a b hab
      (hlip.lipschitzOnWith : LipschitzOnWith 1 gamma (Set.Icc a b))
    simpa using h
  · rcases eq_or_lt_of_le hab with hEq | hlt
    · simp [← hEq]
    · set T : ℝ := b - a with hTdef
      have hT : 0 < T := by rw [hTdef]; linarith
      -- partition bound
      have hpart : ∀ n : ℕ, 0 < n →
          ENNReal.ofReal ((n : ℝ) * (2 * |Real.sin (T / (2 * (n : ℝ)))|))
            ≤ eVariationOn gamma (Set.Icc a b) := by
        intro n hn
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        set u : ℕ → ℝ := fun i => a + min ((i : ℝ) * T / n) T with hudef
        have hmono : Monotone u := by
          intro i j hij
          have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
          have hmul : (i : ℝ) * T ≤ (j : ℝ) * T := mul_le_mul_of_nonneg_right hij' hT.le
          have hdiv : ((i : ℝ) * T / n) ≤ ((j : ℝ) * T / n) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hmul (by positivity)
          simp only [hudef]
          linarith [min_le_min hdiv (le_refl T)]
        have hus : ∀ i, u i ∈ Set.Icc a b := by
          intro i
          constructor
          · simp only [hudef]
            have : (0:ℝ) ≤ min ((i : ℝ) * T / n) T := le_min (by positivity) hT.le
            linarith
          · simp only [hudef]
            linarith [min_le_right ((i : ℝ) * T / n) T]
        have hterm : ∀ i, i < n →
            edist (gamma (u (i + 1))) (gamma (u i))
              = ENNReal.ofReal (2 * |Real.sin (T / (2 * (n : ℝ)))|) := by
          intro i hi
          have hi1 : ((i : ℝ) + 1) * T / n ≤ T := by
            have : ((i : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hi
            rw [div_le_iff₀ hnR]
            nlinarith [this, hT.le]
          have hi0 : (i : ℝ) * T / n ≤ T := by
            have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.le
            rw [div_le_iff₀ hnR]
            nlinarith [this, hT.le]
          have hu1 : u (i + 1) = a + ((i : ℝ) + 1) * T / n := by
            simp only [hudef]
            push_cast
            rw [min_eq_left hi1]
          have hu0 : u i = a + (i : ℝ) * T / n := by
            simp only [hudef, min_eq_left hi0]
          rw [edist_dist, hgdef,
            SphericalGeometry.dist_greatCirclePath v1 v2 h1 h2 ho (u (i + 1)) (u i),
            hu1, hu0]
          congr 2
          have : (a + ((i : ℝ) + 1) * T / n - (a + (i : ℝ) * T / n)) = T / n := by
            field_simp
            ring
          rw [this]
          congr 1
          field_simp
        have hsum := eVariationOn.sum_le (f := gamma) (s := Set.Icc a b) (n := n) hmono hus
        have hcalc : (∑ i ∈ Finset.range n,
            edist (gamma (u (i + 1))) (gamma (u i)))
            = ENNReal.ofReal ((n : ℝ) * (2 * |Real.sin (T / (2 * (n : ℝ)))|)) := by
          rw [Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi)),
            Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        rw [hcalc] at hsum
        exact hsum
      -- the partition sums converge to T
      have hslope : Filter.Tendsto (fun x : ℝ => Real.sin x / x)
          (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
        have hd := Real.hasDerivAt_sin 0
        rw [Real.cos_zero] at hd
        have ht := hasDerivAt_iff_tendsto_slope.mp hd
        simpa [slope_fun_def_field, Real.sin_zero] using ht
      have hx : Filter.Tendsto (fun n : ℕ => T / (2 * (n : ℝ))) atTop
          (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop := by
            exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
          exact Filter.Tendsto.div_atTop tendsto_const_nhds this
        · filter_upwards [eventually_gt_atTop 0] with n hn
          have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          positivity
      have hlim : Filter.Tendsto
          (fun n : ℕ => (n : ℝ) * (2 * |Real.sin (T / (2 * (n : ℝ)))|)) atTop (nhds T) := by
        have hcomp := hslope.comp hx
        have heq : (fun n : ℕ => (n : ℝ) * (2 * |Real.sin (T / (2 * (n : ℝ)))|))
            =ᶠ[atTop] (fun n : ℕ => T * ((fun x : ℝ => Real.sin x / x)
              (T / (2 * (n : ℝ))))) := by
          filter_upwards [eventually_gt_atTop (Nat.ceil (T / Real.pi) + 1)] with n hn
          have hn0 : 0 < n := by omega
          have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
          have hxpos : 0 < T / (2 * (n : ℝ)) := by positivity
          have hxlt : T / (2 * (n : ℝ)) < Real.pi := by
            rw [div_lt_iff₀ (by positivity)]
            have h1 : (T / Real.pi) < (n : ℝ) := by
              have := Nat.lt_of_succ_le hn
              have hcl : T / Real.pi ≤ (Nat.ceil (T / Real.pi) : ℝ) := Nat.le_ceil _
              have : ((Nat.ceil (T / Real.pi) : ℕ) : ℝ) < (n : ℝ) := by
                exact_mod_cast (by omega : Nat.ceil (T / Real.pi) < n)
              linarith
            rw [div_lt_iff₀ Real.pi_pos] at h1
            nlinarith [h1, Real.pi_pos, hnR]
          have hsinpos : 0 < Real.sin (T / (2 * (n : ℝ))) :=
            Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
          rw [abs_of_pos hsinpos]
          field_simp
        have hfin : Filter.Tendsto
            (fun n : ℕ => T * ((fun x : ℝ => Real.sin x / x) (T / (2 * (n : ℝ)))))
            atTop (nhds (T * 1)) := Filter.Tendsto.const_mul T hcomp
        rw [mul_one] at hfin
        exact hfin.congr' heq.symm
      have hofr : Filter.Tendsto
          (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * (2 * |Real.sin (T / (2 * (n : ℝ)))|)))
          atTop (nhds (ENNReal.ofReal T)) := ENNReal.tendsto_ofReal hlim
      refine le_of_tendsto hofr ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact hpart n hn
