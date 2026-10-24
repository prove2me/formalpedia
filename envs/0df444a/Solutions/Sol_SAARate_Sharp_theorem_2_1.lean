-- Prove2me | solution 1 for SAARate.Sharp.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T12:12:46.109801+00:00
-- url     : https://prove2.me/submissions/2c299660-260a-47f2-9406-e99a43053a86

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open SAARate.Sharp
namespace SharpSAAProof
end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open SAARate.Sharp
namespace SharpSAAProof

variable {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g) (x d : E m)
include hg

lemma line_convex : ConvexOn ℝ Set.univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb u v hu hv huv
  have he : x + (u * a + v * b) • d = u • (x + a • d) + v • (x + b • d) := by
    match_scalars <;> nlinarith [huv]
  simpa only [smul_eq_mul, he] using hg.2 (Set.mem_univ (x + a • d))
    (Set.mem_univ (x + b • d)) hu hv huv

lemma directional_tendsto : Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
    (𝓝[>] (0 : ℝ)) (𝓝 (dirDeriv g x d)) := by
  have hd := (line_convex g hg x d).hasDerivWithinAt_sInf_slope_of_mem_interior
    (x := 0) (by simp)
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hd
  have hfun : slope (fun t : ℝ => g (x + t • d)) 0 = (fun t : ℝ => (g (x + t • d) - g x) / t) := by
    funext t
    simp only [slope_def_field, zero_smul, add_zero, sub_zero]
  rw [hfun] at hl
  have he := hl.limUnder_eq
  change Tendsto _ _ (𝓝 (limUnder _ _))
  rw [he]
  exact hl

lemma secant_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    g x - g (x - d) ≤ (g (x + t • d) - g x) / t ∧
      (g (x + t • d) - g x) / t ≤ g (x + d) - g x := by
  constructor
  · have hden : 0 < 1 + t := by linarith
    have ha : 0 ≤ t / (1 + t) := div_nonneg ht.le hden.le
    have hb : 0 ≤ 1 / (1 + t) := div_nonneg zero_le_one hden.le
    have hab : t / (1 + t) + 1 / (1 + t) = 1 := by field_simp; ring
    have he : (t / (1 + t)) • (x - d) + (1 / (1 + t)) • (x + t • d) = x := by
      match_scalars <;> field_simp <;> ring
    have h := hg.2 (Set.mem_univ (x - d)) (Set.mem_univ (x + t • d)) ha hb hab
    rw [he] at h
    simp only [smul_eq_mul] at h
    have h' : (1 + t) * g x ≤ t * g (x - d) + g (x + t • d) := by
      rw [mul_comm (1 + t)]
      apply (le_div_iff₀ hden).mp
      convert h using 1
      field_simp
    apply (le_div_iff₀ ht).mpr
    nlinarith
  · have he : (1 - t) • x + t • (x + d) = x + t • d := by module
    have h := hg.2 (Set.mem_univ x) (Set.mem_univ (x + d))
      (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
    rw [he] at h
    simp only [smul_eq_mul] at h
    apply (div_le_iff₀ ht).mpr
    nlinarith

lemma directional_le_secant : dirDeriv g x d ≤ g (x + d) - g x := by
  apply le_of_tendsto (directional_tendsto g hg x d)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  exact (secant_bounds g hg x d ht ht1.le).2

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open SAARate.Sharp
namespace SharpSAAProof
variable {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g) (x : E m)
include hg

lemma directional_zero : dirDeriv g x 0 = 0 := by
  have h := directional_tendsto g hg x 0
  simp only [smul_zero, add_zero, sub_self, zero_div] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

omit hg in
lemma positive_scale_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => a * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (tendsto_const_nhds.mul nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => a * t) (𝓝[>] (0 : ℝ)) (𝓝 (a * 0)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ha ht

lemma directional_smul (d : E m) (a : ℝ) (ha : 0 ≤ a) :
    dirDeriv g x (a • d) = a * dirDeriv g x d := by
  rcases eq_or_lt_of_le ha with ha | ha
  · subst a
    simp [directional_zero g hg x]
  · have hs := (directional_tendsto g hg x d).comp (positive_scale_tendsto a ha)
    have ht := hs.const_mul a
    have he : (fun t : ℝ => (g (x + t • (a • d)) - g x) / t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => a * ((g (x + (a * t) • d) - g x) / (a * t))) := by
      filter_upwards [self_mem_nhdsWithin] with t hpos
      rw [smul_smul, mul_comm t a]
      field_simp [ha.ne', (show 0 < t from hpos).ne']
    exact tendsto_nhds_unique (directional_tendsto g hg x (a • d)) (ht.congr' he.symm)

lemma directional_add_le (d e : E m) :
    dirDeriv g x (d + e) ≤ dirDeriv g x d + dirDeriv g x e := by
  have hd := (directional_tendsto g hg x d).comp (positive_scale_tendsto 2 (by norm_num))
  have he := (directional_tendsto g hg x e).comp (positive_scale_tendsto 2 (by norm_num))
  apply le_of_tendsto_of_tendsto (directional_tendsto g hg x (d + e)) (hd.add he)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hid : (1 / 2 : ℝ) • (x + (2 * t) • d) + (1 / 2 : ℝ) • (x + (2 * t) • e) =
      x + t • (d + e) := by module
  have hc := hg.2 (Set.mem_univ (x + (2 * t) • d))
    (Set.mem_univ (x + (2 * t) • e)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [hid] at hc
  simp only [smul_eq_mul] at hc
  change (g (x + t • (d + e)) - g x) / t ≤
    (g (x + (2 * t) • d) - g x) / (2 * t) + (g (x + (2 * t) • e) - g x) / (2 * t)
  have heq : (g (x + (2 * t) • d) - g x) / (2 * t) + (g (x + (2 * t) • e) - g x) / (2 * t) =
    ((1 / 2) * g (x + (2 * t) • d) + (1 / 2) * g (x + (2 * t) • e) - g x) / t := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hc _) ht.le

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology SAARate.Sharp
namespace SharpSAAProof

def directionalEnvelope {m : ℕ} {Ω : Type*}
    (h : E m → Ω → ℝ) (x : E m) (w : Ω) : ℝ :=
  ∑ i : Fin m,
    (|dirDeriv (fun y => h y w) x (EuclideanSpace.basisFun (Fin m) ℝ i)| +
     |dirDeriv (fun y => h y w) x (-(EuclideanSpace.basisFun (Fin m) ℝ i))|)

theorem quotient_abs_bound {m : ℕ} (g : E m → ℝ)
    (hg : ConvexOn ℝ Set.univ g) (x d : E m) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |(g (x + t • d) - g x) / t| ≤ |g (x + d) - g x| + |g (x - d) - g x| := by
  have hb := secant_bounds g hg x d ht ht1
  have h1 := le_abs_self (g (x + d) - g x)
  have h2 := le_abs_self (g (x - d) - g x)
  have h3 := abs_nonneg (g (x + d) - g x)
  have h4 := abs_nonneg (g (x - d) - g x)
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem derivative_integrable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (x d : E m) :
    Integrable (fun w => dirDeriv (fun y => h y w) x d) P := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Ω → ℝ := fun n w => (h (x + t n • d) w - h x w) / t n
  let C : Ω → ℝ := fun w => |h (x + d) w - h x w| + |h (x - d) w - h x w|
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hts : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall ht)
  have hF (n : ℕ) : Integrable (F n) P :=
    ((hint (x + t n • d)).sub (hint x)).div_const (t n)
  have hlim (w : Ω) : Tendsto (fun n => F n w) atTop
      (𝓝 (dirDeriv (fun y => h y w) x d)) :=
    (directional_tendsto (fun y => h y w) (hconv w) x d).comp hts
  have hC : Integrable C P :=
    ((hint (x + d)).sub (hint x)).abs.add (((hint (x - d)).sub (hint x)).abs)
  have hb (n : ℕ) (w : Ω) : ‖F n w‖ ≤ C w := by
    exact quotient_abs_bound (fun y => h y w) (hconv w) x d (ht n) (ht1 n)
  apply hC.mono'
  · exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hF n).aestronglyMeasurable) (ae_of_all P hlim)
  · exact ae_of_all P (fun w => le_of_tendsto (hlim w).norm
      (Eventually.of_forall (fun n => hb n w)))

theorem envelope_nonneg {m : ℕ} {Ω : Type*}
    (h : E m → Ω → ℝ) (x : E m) (w : Ω) :
    0 ≤ directionalEnvelope h x w := by
  exact Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem envelope_integrable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (x : E m) :
    Integrable (directionalEnvelope h x) P := by
  exact integrable_finsetSum _ (fun i _ =>
    (derivative_integrable P h hconv hint x (EuclideanSpace.basisFun (Fin m) ℝ i)).abs.add
      (derivative_integrable P h hconv hint x (-(EuclideanSpace.basisFun (Fin m) ℝ i))).abs)

theorem directional_sum_le {m : ℕ} (g : E m → ℝ)
    (hg : ConvexOn ℝ Set.univ g) (x : E m) {ι : Type*}
    (s : Finset ι) (v : ι → E m) :
    dirDeriv g x (∑ i ∈ s, v i) ≤ ∑ i ∈ s, dirDeriv g x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [directional_zero g hg x]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (directional_add_le g hg x (v a) (∑ i ∈ s, v i)).trans (add_le_add le_rfl ih)

theorem directional_envelope_upper {m : ℕ} {Ω : Type*}
    (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (x : E m) (w : Ω) (v : E m) :
    dirDeriv (fun y => h y w) x v ≤ directionalEnvelope h x w * ‖v‖ := by
  let g := fun y => h y w
  let e := EuclideanSpace.basisFun (Fin m) ℝ
  let B : Fin m → ℝ := fun i => |dirDeriv g x (e i)| + |dirDeriv g x (-e i)|
  have hB (i : Fin m) : 0 ≤ B i := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hc (i : Fin m) : dirDeriv g x (v i • e i) ≤ |v i| * B i := by
    by_cases hi : 0 ≤ v i
    · rw [directional_smul g (hconv w) x (e i) (v i) hi, abs_of_nonneg hi]
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))) hi
    · have hn : v i < 0 := lt_of_not_ge hi
      have he : v i • e i = (-v i) • (-e i) := by simp
      rw [he, directional_smul g (hconv w) x (-e i) (-v i) (by linarith), abs_of_neg hn]
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) (by linarith)
  have hr : (∑ i : Fin m, v i • e i) = v := by
    exact e.sum_repr v
  calc
    dirDeriv g x v = dirDeriv g x (∑ i : Fin m, v i • e i) := congrArg _ hr.symm
    _ ≤ ∑ i : Fin m, dirDeriv g x (v i • e i) := directional_sum_le g (hconv w) x _ _
    _ ≤ ∑ i : Fin m, |v i| * B i := Finset.sum_le_sum (fun i _ => hc i)
    _ ≤ ∑ i : Fin m, ‖v‖ * B i := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (hB i))
    _ = directionalEnvelope h x w * ‖v‖ := by
      rw [← Finset.mul_sum]
      exact mul_comm _ _

theorem envelope_lipschitz {m : ℕ} {Ω : Type*}
    (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (x : E m) (w : Ω) (d e : E m) :
    |dirDeriv (fun y => h y w) x d - dirDeriv (fun y => h y w) x e|
      ≤ directionalEnvelope h x w * ‖d - e‖ := by
  have h1 := directional_add_le (fun y => h y w) (hconv w) x e (d - e)
  have h2 := directional_add_le (fun y => h y w) (hconv w) x d (e - d)
  have he : e + (d - e) = d := by abel
  have hd : d + (e - d) = e := by abel
  rw [he] at h1
  rw [hd] at h2
  have h3 := directional_envelope_upper h hconv x w (d - e)
  have h4 := directional_envelope_upper h hconv x w (e - d)
  rw [norm_sub_rev] at h4
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology SAARate.Sharp
namespace SharpSAAProof

theorem expectedObj_convex {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) :
    ConvexOn ℝ Set.univ (expectedObj P h) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := integral_mono (hint (a • x + b • y))
    (((hint x).const_mul a).add ((hint y).const_mul b))
    (fun w => (hconv w).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab)
  simpa only [Pi.add_apply, expectedObj, integral_add ((hint x).const_mul a) ((hint y).const_mul b),
    integral_const_mul, smul_eq_mul] using hh

theorem expectation_dirDeriv {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (x d : E m) :
    dirDeriv (expectedObj P h) x d =
      ∫ w, dirDeriv (fun y => h y w) x d ∂P := by
  let F : ℝ → Ω → ℝ := fun t w => (h (x + t • d) w - h x w) / t
  let C : Ω → ℝ := fun w => |h (x + d) w - h x w| + |h (x - d) w - h x w|
  have hC : Integrable C P :=
    ((hint (x + d)).sub (hint x)).abs.add (((hint (x - d)).sub (hint x)).abs)
  have hF (t : ℝ) : Integrable (F t) P :=
    ((hint (x + t • d)).sub (hint x)).div_const t
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ w ∂P, ‖F t w‖ ≤ C w := by
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 :=
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hle] with t ht ht1
    exact ae_of_all P (fun w => quotient_abs_bound (fun y => h y w) (hconv w) x d ht ht1)
  have hl := tendsto_integral_filter_of_dominated_convergence C
    (Eventually.of_forall (fun t => (hF t).aestronglyMeasurable)) hb hC
    (ae_of_all P (fun w => directional_tendsto (fun y => h y w) (hconv w) x d))
  have he (t : ℝ) : (∫ w, F t w ∂P) =
      (expectedObj P h (x + t • d) - expectedObj P h x) / t := by
    simp only [F, expectedObj, integral_div, integral_sub (hint (x + t • d)) (hint x)]
  simp_rw [he] at hl
  exact hl.limUnder_eq

theorem expected_directional_lipschitz {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (x d e : E m) :
    |dirDeriv (expectedObj P h) x d - dirDeriv (expectedObj P h) x e|
      ≤ (∫ w, directionalEnvelope h x w ∂P) * ‖d - e‖ := by
  rw [expectation_dirDeriv P h hconv hint x d, expectation_dirDeriv P h hconv hint x e,
    ← integral_sub (derivative_integrable P h hconv hint x d)
      (derivative_integrable P h hconv hint x e)]
  calc
    _ ≤ ∫ w, |dirDeriv (fun y => h y w) x d - dirDeriv (fun y => h y w) x e| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w, directionalEnvelope h x w * ‖d - e‖ ∂P :=
      integral_mono ((derivative_integrable P h hconv hint x d).sub
        (derivative_integrable P h hconv hint x e)).abs
        ((envelope_integrable P h hconv hint x).mul_const _) (fun w => envelope_lipschitz h hconv x w d e)
    _ = _ := integral_mul_const _ _

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology SAARate.Sharp
namespace SharpSAAProof

theorem iid_average {Ω : Type*} {S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Q : Measure S) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω)
    (g : Ω → ℝ) (hg : Integrable g P) :
    ∀ᵐ s ∂Q, Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g (ω j s))
      atTop (𝓝 (∫ w, g w ∂P)) := by
  have hid (j : ℕ) : IdentDistrib (ω j) id Q P :=
    ⟨(hω.1 j).aemeasurable, aemeasurable_id, by simpa using hω.2.2 j⟩
  have hcomp (j : ℕ) : IdentDistrib (fun s => g (ω j s)) g Q P := by
    have hm : AEMeasurable g (Q.map (ω j)) := by
      rw [hω.2.2 j]
      exact hg.aestronglyMeasurable.aemeasurable
    simpa only [Function.comp_def, id_eq] using (hid j).comp_of_aemeasurable hm
  have hi : iIndepFun (fun j s => g (ω j s)) Q := by
    exact hω.2.1.comp₀ (fun _ => g) (fun j => (hω.1 j).aemeasurable)
      (fun j => by rw [hω.2.2 j]; exact hg.aestronglyMeasurable.aemeasurable)
  have hh := strong_law_ae_real (fun j s => g (ω j s))
    ((hcomp 0).integrable_iff.mpr hg)
    (fun _ _ hij => hi.indepFun hij)
    (fun j => (hcomp j).trans (hcomp 0).symm)
  filter_upwards [hh] with s hs
  simpa only [div_eq_mul_inv, mul_comm, (hcomp 0).integral_eq] using hs

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology SAARate.Sharp
namespace SharpSAAProof

theorem average_directional_lipschitz {m : ℕ} {Ω : Type*}
    (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (x : E m) (ω : ℕ → Ω) (N : ℕ) (d e : E m) :
    |(N : ℝ)⁻¹ * (∑ j ∈ Finset.range N, dirDeriv (fun y => h y (ω j)) x d) -
      (N : ℝ)⁻¹ * (∑ j ∈ Finset.range N, dirDeriv (fun y => h y (ω j)) x e)|
      ≤ ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, directionalEnvelope h x (ω j)) * ‖d - e‖ := by
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        |dirDeriv (fun y => h y (ω j)) x d - dirDeriv (fun y => h y (ω j)) x e| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, directionalEnvelope h x (ω j) * ‖d - e‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum
        (fun j _ => envelope_lipschitz h hconv x (ω j) d e)) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

theorem uniform_derivative_average {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (x : E m)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ s ∂Q, ∀ᶠ (N : ℕ) in atTop, ∀ d : E m, ‖d‖ ≤ 1 →
      |(N : ℝ)⁻¹ * (∑ j ∈ Finset.range N,
          dirDeriv (fun y => h y (ω j s)) x d) -
        dirDeriv (expectedObj P h) x d| < ε := by
  classical
  let M : ℝ := ∫ w, directionalEnvelope h x w ∂P
  have hM : 0 ≤ M := integral_nonneg (envelope_nonneg h x)
  let η : ℝ := ε / (4 * (2 * M + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨net, hnet⟩ := (isCompact_closedBall (0 : E m) 1).elim_finite_subcover
    (fun q : E m => Metric.ball q η) (fun _ => Metric.isOpen_ball)
    (by intro d _; exact Set.mem_iUnion.mpr ⟨d, Metric.mem_ball_self hη⟩)
  let A : S → ℕ → E m → ℝ := fun s N d =>
    (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, dirDeriv (fun y => h y (ω j s)) x d
  let B : S → ℕ → ℝ := fun s N =>
    (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, directionalEnvelope h x (ω j s)
  let D : E m → ℝ := fun d => dirDeriv (expectedObj P h) x d
  have hp (q : E m) : ∀ᵐ s ∂Q, Tendsto (fun N => A s N q) atTop (𝓝 (D q)) := by
    simpa only [A, D, ← expectation_dirDeriv P h hconv hint x q] using
      iid_average P Q ω hω (fun w => dirDeriv (fun y => h y w) x q)
        (derivative_integrable P h hconv hint x q)
  have hps : ∀ᵐ s ∂Q, ∀ q ∈ net, Tendsto (fun N => A s N q) atTop (𝓝 (D q)) :=
    net.eventually_all.mpr (fun q _ => hp q)
  have hbs : ∀ᵐ s ∂Q, Tendsto (B s) atTop (𝓝 M) :=
    iid_average P Q ω hω (directionalEnvelope h x) (envelope_integrable P h hconv hint x)
  filter_upwards [hps, hbs] with s hsp hsb
  have he : ∀ᶠ N in atTop, ∀ q ∈ net, |A s N q - D q| < ε / 2 := by
    apply net.eventually_all.mpr
    intro q hq
    have ht : Tendsto (fun N => |A s N q - D q|) atTop (𝓝 0) := by
      simpa using ((hsp q hq).sub_const (D q)).abs
    exact ht.eventually_lt_const (half_pos hε)
  have hbe : ∀ᶠ N in atTop, B s N ≤ M + 1 := hsb.eventually_le_const (lt_add_one M)
  filter_upwards [he, hbe] with N hN hBN
  intro d hd
  have hd' : d ∈ Metric.closedBall (0 : E m) 1 := by simpa using hd
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hnet hd')
  obtain ⟨hqnet, hqd⟩ := Set.mem_iUnion.mp hq
  have hdist : ‖d - q‖ < η := by simpa only [Metric.mem_ball, dist_eq_norm] using hqd
  have h1 := average_directional_lipschitz h hconv x (fun j => ω j s) N d q
  have h2 := expected_directional_lipschitz P h hconv hint x q d
  rw [norm_sub_rev] at h2
  have htri : |A s N d - D d| ≤ |A s N d - A s N q| + |A s N q - D q| + |D q - D d| := by
    calc
      _ = |(A s N d - A s N q) + (A s N q - D q) + (D q - D d)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hnorm : 0 ≤ ‖d - q‖ := norm_nonneg _
  have hmul : (B s N + M) * ‖d - q‖ ≤ (2 * M + 1) * ‖d - q‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hnorm
  have hstrict : (2 * M + 1) * ‖d - q‖ < (2 * M + 1) * η :=
    mul_lt_mul_of_pos_left hdist (by positivity)
  have hηeq : (2 * M + 1) * η = ε / 4 := by
    dsimp [η]
    field_simp [ne_of_gt (show 0 < 2 * M + 1 by positivity)]
  change |A s N d - D d| < ε
  change |A s N d - A s N q| ≤ B s N * ‖d - q‖ at h1
  change |D q - D d| ≤ M * ‖d - q‖ at h2
  rw [hηeq] at hstrict
  have hcenter := hN q hqnet
  nlinarith

end SharpSAAProof
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open SAARate.Sharp
namespace SharpSAAProof

lemma sharp_direction {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (x : E m) (hx : x ∈ Θ)
    (c : ℝ) (hc : ∀ y ∈ Θ, g x + c * ‖y - x‖ ≤ g y)
    (y : E m) (hy : y ∈ Θ) : c * ‖y - x‖ ≤ dirDeriv g x (y - x) := by
  apply ge_of_tendsto (directional_tendsto g hg x (y - x))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  change 0 < t at ht
  have he : (1 - t) • x + t • y = x + t • (y - x) := by module
  have hm : x + t • (y - x) ∈ Θ := by
    rw [← he]
    exact hΘ hx hy (sub_nonneg.mpr ht1.le) ht.le (by ring)
  have h := hc _ hm
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
  apply (le_div_iff₀ ht).mpr
  nlinarith

lemma eventual_unique {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ w, ConvexOn ℝ Set.univ (fun y => h y w))
    (hint : ∀ y, Integrable (h y) P) (Θ : Set (E m)) (hΘ : Convex ℝ Θ)
    (x : E m) (hA : AssumptionA P h Θ x)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, ∀ᶠ N in atTop, argminOn (saaObj h (fun j => ω j s) N) Θ = {x} := by
  obtain ⟨c, hc, hsharp⟩ := hA.sharp
  filter_upwards [uniform_derivative_average P h hconv hint x Q ω hω (c / 2) (by positivity)] with s hs
  filter_upwards [hs, eventually_gt_atTop 0] with N hN hNpos
  have hstrict : ∀ y ∈ Θ, y ≠ x → saaObj h (fun j => ω j s) N x < saaObj h (fun j => ω j s) N y := by
    intro y hy hyx
    let r := ‖y - x‖
    have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    let d := r⁻¹ • (y - x)
    have hd : ‖d‖ = 1 := by simp [d, norm_smul, r, hr.ne']
    have hrd : r • d = y - x := by simp [d, smul_smul, hr.ne']
    have hder := sharp_direction (expectedObj P h) (expectedObj_convex P h hconv hint) Θ hΘ x hA.mem c hsharp y hy
    have hdeq : dirDeriv (expectedObj P h) x (y - x) = r * dirDeriv (expectedObj P h) x d := by
      rw [← hrd, directional_smul (expectedObj P h) (expectedObj_convex P h hconv hint) x d r hr.le]
    rw [hdeq] at hder
    have hdc : c ≤ dirDeriv (expectedObj P h) x d := by
      change c * r ≤ r * dirDeriv (expectedObj P h) x d at hder
      nlinarith
    have herr := (abs_lt.mp (hN d hd.le)).1
    have havg : 0 < (N : ℝ)⁻¹ * (∑ j ∈ Finset.range N, dirDeriv (fun z => h z (ω j s)) x d) := by linarith
    have hsum : (N : ℝ)⁻¹ * (∑ j ∈ Finset.range N, dirDeriv (fun z => h z (ω j s)) x (y - x)) ≤
        saaObj h (fun j => ω j s) N y - saaObj h (fun j => ω j s) N x := by
      unfold saaObj
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      have hxy : x + (y - x) = y := by abel
      simpa only [hxy] using directional_le_secant (fun z => h z (ω j s)) (hconv _) x (y - x)
    have he : (∑ j ∈ Finset.range N, dirDeriv (fun z => h z (ω j s)) x (y - x)) =
        r * (∑ j ∈ Finset.range N, dirDeriv (fun z => h z (ω j s)) x d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hrd, directional_smul (fun z => h z (ω j s)) (hconv _) x d r hr.le]
    rw [he] at hsum
    have hp := mul_pos hr havg
    nlinarith
  apply Set.ext
  intro y
  constructor
  · intro hy
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact (not_lt_of_ge (hy.2 x hA.mem)) (hstrict y hy.1 hne)
  · intro hy
    have hyx := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨hA.mem, ?_⟩
    intro y hy
    by_cases he : y = x
    · subst y; exact le_rfl
    · exact (hstrict y hy he).le

end SharpSAAProof
end

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_2_1 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : E m) (hA : AssumptionA P h Θ xbar)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, ∀ᶠ N in atTop, argminOn (saaObj h (fun j => ω j s) N) Θ = {xbar} := by
  have _ := hΘc
  exact SharpSAAProof.eventual_unique P h hconv hint Θ hΘv xbar hA Q ω hω

end SAARate.Sharp

open SAARate.Sharp


open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : E m) (hA : AssumptionA P h Θ xbar)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ᵐ s ∂Q, ∀ᶠ N in atTop, argminOn (saaObj h (fun j => ω j s) N) Θ = {xbar} := by
  exact SAARate.Sharp.theorem_2_1 P h hconv hint Θ hΘc hΘv xbar hA Q ω hω
