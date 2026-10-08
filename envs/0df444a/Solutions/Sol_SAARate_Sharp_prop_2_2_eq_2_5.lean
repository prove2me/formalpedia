-- Prove2me | solution 1 for SAARate.Sharp.prop_2_2_eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:14:45.376344+00:00
-- url     : https://prove2.me/submissions/acd78c39-0b0e-4978-977f-6f85fd5e99eb

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

open SAARate.Sharp Filter Set
open scoped Topology

theorem line_convex {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    ConvexOn ℝ univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ u v hu hv huv
  have hh := hg.2 (mem_univ (x + a • d)) (mem_univ (x + b • d)) hu hv huv
  have he : u • (x + a • d) + v • (x + b • d) = x + (u * a + v * b) • d := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    calc
      u • x + (u * a) • d + (v • x + (v * b) • d) =
          (u + v) • x + (u * a + v * b) • d := by module
      _ = x + (u * a + v * b) • d := by rw [huv, one_smul]
  rw [he] at hh
  simpa only [smul_eq_mul] using hh

theorem quotient_tendsto {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g) (x d : E m) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (dirDeriv g x d)) := by
  let f : ℝ → ℝ := fun t => g (x + t • d)
  have hd := (line_convex g hg x d).hasDerivWithinAt_rightDeriv_of_mem_interior
    (x := (0 : ℝ)) (by simp)
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hd
  have hl' : Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (derivWithin f (Ioi 0) 0)) := by
    simpa only [slope_fun_def_field, sub_zero, zero_smul, add_zero] using hl
  have he : dirDeriv g x d = derivWithin f (Ioi 0) 0 := by
    exact hl'.limUnder_eq
  rwa [he]

open MeasureTheory ProbabilityTheory

private theorem quotient_bound {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ univ g)
    (x d : E m) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖(g (x + t • d) - g x) / t‖ ≤ |g (x + d) - g x| + |g x - g (x - d)| := by
  have hc := line_convex g hg x d
  have hlo := hc.slope_mono (mem_univ 0)
    (show (-1 : ℝ) ∈ Set.diff univ {0} from ⟨mem_univ _, by simpa using (show (-1 : ℝ) ≠ 0 by norm_num)⟩)
    (show t ∈ Set.diff univ {0} from ⟨mem_univ _, by simpa using ht.ne'⟩) (by linarith : -1 ≤ t)
  have hhi := hc.slope_mono (mem_univ 0)
    (show t ∈ Set.diff univ {0} from ⟨mem_univ _, by simpa using ht.ne'⟩)
    (show (1 : ℝ) ∈ Set.diff univ {0} from ⟨mem_univ _, by simpa using (show (1 : ℝ) ≠ 0 by norm_num)⟩) ht1
  simp only [slope_def_field, sub_zero, zero_smul, add_zero, one_smul,
    neg_smul, one_smul, div_neg, div_one, ← sub_eq_add_neg] at hlo hhi
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have := neg_le_abs (g x - g (x - d))
    have := abs_nonneg (g (x + d) - g x)
    linarith
  · have := le_abs_self (g (x + d) - g x)
    have := abs_nonneg (g x - g (x - d))
    linarith

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop_2_2_eq_2_5 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P) :
    ∀ x d : E m, Integrable (fun ω => dirDeriv (fun y => h y ω) x d) P ∧
      dirDeriv (expectedObj P h) x d = ∫ ω, dirDeriv (fun y => h y ω) x d ∂P := by
  intro x d
  let F : ℝ → Ω → ℝ := fun t ω => (h (x + t • d) ω - h x ω) / t
  let B : Ω → ℝ := fun ω => |h (x + d) ω - h x ω| + |h x ω - h (x - d) ω|
  have hB : Integrable B P := ((hint (x + d)).sub (hint x)).abs.add
    ((hint x).sub (hint (x - d))).abs
  have hmeas (t : ℝ) : AEStronglyMeasurable (F t) P :=
    (((hint (x + t • d)).sub (hint x)).div_const t).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun t => F t ω) (𝓝[>] 0)
      (𝓝 (dirDeriv (fun y => h y ω) x d)) :=
    ae_of_all P (fun ω => quotient_tendsto _ (hconv ω) x d)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)
      |>.filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht, ht1.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂P, ‖F t ω‖ ≤ B ω := by
    filter_upwards [hsmall] with t ht
    exact ae_of_all P (fun ω => quotient_bound _ (hconv ω) x d t ht.1 ht.2)
  have hm : AEStronglyMeasurable (fun ω => dirDeriv (fun y => h y ω) x d) P :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) hmeas hlim
  have hi : Integrable (fun ω => dirDeriv (fun y => h y ω) x d) P := by
    apply hB.mono' hm
    exact ae_of_all P fun ω => le_of_tendsto (quotient_tendsto _ (hconv ω) x d).norm
      (hsmall.mono fun t ht => quotient_bound _ (hconv ω) x d t ht.1 ht.2)
  have hl := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hmeas) hbound hB hlim
  have hl' : Tendsto (fun t : ℝ => (expectedObj P h (x + t • d) - expectedObj P h x) / t)
      (𝓝[>] 0) (𝓝 (∫ ω, dirDeriv (fun y => h y ω) x d ∂P)) := by
    convert hl using 1
    funext t
    simp only [F, expectedObj, integral_div, integral_sub (hint _) (hint _)]
  exact ⟨hi, hl'.limUnder_eq⟩


end SAARate.Sharp

theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P) :
    ∀ x d : E m, Integrable (fun ω => dirDeriv (fun y => h y ω) x d) P ∧
      dirDeriv (expectedObj P h) x d = ∫ ω, dirDeriv (fun y => h y ω) x d ∂P  := by
  exact SAARate.Sharp.prop_2_2_eq_2_5 P h hconv hint

#print axioms solution
