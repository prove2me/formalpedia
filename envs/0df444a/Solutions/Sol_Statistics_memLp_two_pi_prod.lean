-- Prove2me | solution 1 for Statistics.memLp_two_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T17:34:51.902349+00:00
-- url     : https://prove2.me/submissions/49c682db-bb67-459b-8816-0f8b728a1547

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

section

open MeasureTheory Measure
open scoped ENNReal

namespace Statistics

/-- **Tonelli for finite products**: the `ℝ≥0∞`-integral of a product of coordinatewise
functions over a product measure is the product of the integrals. -/
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmp := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
      have hg : Measurable (fun q : E 0 × ((j : Fin n) → E ((0 : Fin (n+1)).succAbove j)) =>
          f 0 q.1 * ∏ j, f ((0 : Fin (n+1)).succAbove j) (q.2 j)) := by
        refine Measurable.mul ((hf 0).comp measurable_fst) ?_
        exact Finset.measurable_prod _ fun j _ =>
          (hf _).comp ((measurable_pi_apply j).comp measurable_snd)
      have hcomp := hmp.lintegral_comp hg
      have heq : ∀ a : (j : Fin (n + 1)) → E j,
          f 0 ((MeasurableEquiv.piFinSuccAbove E 0) a).1 *
            ∏ j, f ((0 : Fin (n+1)).succAbove j) (((MeasurableEquiv.piFinSuccAbove E 0) a).2 j)
          = ∏ i, f i (a i) := by
        intro a
        rw [Fin.prod_univ_succAbove (fun i => f i (a i)) 0]
        rfl
      simp only [heq] at hcomp
      rw [hcomp]
      rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ ((0 : Fin (n+1)).succAbove j))
          (f := fun x => f 0 x) (g := fun h => ∏ j, f ((0 : Fin (n+1)).succAbove j) (h j))
          (hf 0).aemeasurable
          (Finset.measurable_prod _ fun j _ =>
            (hf _).comp (measurable_pi_apply j)).aemeasurable]
      rw [ih (fun j => hf ((0 : Fin (n+1)).succAbove j)),
        Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂(μ i)) 0]

/-- **A product of densities is the density of the product**: forming a product measure
commutes with tilting each factor by a density. -/
theorem pi_withDensity {n : ℕ} {E : Type*} [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (g : Fin n → E → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hfin : ∀ i, SigmaFinite ((μ i).withDensity (g i))) :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun p => ∏ i, g i (p i)) := by
  haveI := hfin
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (g i)) fun s hs => ?_
  have hms : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hms, ← lintegral_indicator hms]
  have hind : ∀ p : Fin n → E, (Set.univ.pi s).indicator (fun p => ∏ i, g i (p i)) p
      = ∏ i, (s i).indicator (g i) (p i) := by
    intro p
    by_cases hp : p ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hp]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (Set.indicator_of_mem (hp i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hp]
      simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hp
      obtain ⟨i, hi⟩ := hp
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      exact Set.indicator_of_notMem hi _
  simp only [hind]
  rw [lintegral_fin_nat_prod (E := fun _ => E) (μ := μ) (f := fun i => (s i).indicator (g i))
    (fun i => (hg i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

section Deriv

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The product of a coordinatewise family of `L²` functions is `L²` for the product measure. -/
lemma memLp_two_pi_prod_aux (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (Ψ : Ω → ℝ)
    (hΨmeas : Measurable Ψ) (hΨ : MemLp Ψ 2 μ) :
    MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 (Measure.pi fun _ : Fin T => μ) := by
  have hsq : Integrable (fun x => Ψ x * Ψ x) μ := hΨ.integrable_mul hΨ
  have hprod : Integrable (fun p : Fin T → Ω => ∏ i, (Ψ (p i) * Ψ (p i)))
      (Measure.pi fun _ : Fin T => μ) :=
    Integrable.fintype_prod (f := fun _ : Fin T => fun x => Ψ x * Ψ x) (fun _ => hsq)
  have hmeasP : Measurable (fun p : Fin T → Ω => ∏ i, Ψ (p i)) :=
    Finset.measurable_prod _ fun i _ => hΨmeas.comp (measurable_pi_apply i)
  refine (memLp_two_iff_integrable_sq hmeasP.aestronglyMeasurable).2 (hprod.congr ?_)
  filter_upwards with p
  rw [sq, ← Finset.prod_mul_distrib]

/-- **Differentiation under the integral sign for an i.i.d. tilted family.**  If each
coordinate density `L t` is differentiable in `t` with derivative and value dominated by a
single `L²` envelope `Ψ ≥ 1`, then the expectation of `D` against the tilted product measure
is differentiable at `t = 0`, with the derivative given by the sum of the coordinatewise
scores. -/
theorem hasDerivAt_integral_pi_mul (μ : Measure Ω) [IsProbabilityMeasure μ] {T : ℕ}
    (L L' : ℝ → Ω → ℝ) (D : (Fin T → Ω) → ℝ) {ε : ℝ} (hε : 0 < ε) (Ψ : Ω → ℝ)
    (hL0 : ∀ x, L 0 x = 1)
    (hLmeas : ∀ t, Measurable (L t)) (hL'meas : Measurable (L' 0))
    (hDmeas : Measurable D)
    (hD : MemLp D 2 (Measure.pi fun _ : Fin T => μ))
    (hderiv : ∀ (x : Ω) (t : ℝ), |t| < ε → HasDerivAt (fun t => L t x) (L' t x) t)
    (hΨ1 : ∀ x, 1 ≤ Ψ x)
    (hLbound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L t x| ≤ Ψ x)
    (hL'bound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L' t x| ≤ Ψ x)
    (hΨmeas : Measurable Ψ) (hΨL2 : MemLp Ψ 2 μ) :
    HasDerivAt (fun t => ∫ p, D p * ∏ i, L t (p i) ∂(Measure.pi fun _ : Fin T => μ))
      (∫ p, D p * ∑ i : Fin T, L' 0 (p i) ∂(Measure.pi fun _ : Fin T => μ)) 0 := by
  classical
  set P : Measure (Fin T → Ω) := Measure.pi fun _ : Fin T => μ with hP
  set F : ℝ → (Fin T → Ω) → ℝ := fun t p => D p * ∏ i, L t (p i) with hF
  set F' : ℝ → (Fin T → Ω) → ℝ := fun t p =>
    D p * ∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i) with hF'
  set bound : (Fin T → Ω) → ℝ := fun p => |D p| * ((T : ℝ) * ∏ j, Ψ (p j)) with hbound
  have hLmeasP : ∀ t : ℝ, Measurable (fun p : Fin T → Ω => ∏ i, L t (p i)) := fun t =>
    Finset.measurable_prod _ fun i _ => (hLmeas t).comp (measurable_pi_apply i)
  have hFmeas : ∀ t : ℝ, Measurable (F t) := fun t => hDmeas.mul (hLmeasP t)
  have hF'meas : Measurable (F' 0) := by
    refine hDmeas.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (Finset.measurable_prod _ fun j _ => (hLmeas 0).comp (measurable_pi_apply j)).mul
      (hL'meas.comp (measurable_pi_apply i))
  have hF0 : F 0 = D := by
    funext p; simp [hF, hL0]
  have hΨprod : MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 P :=
    memLp_two_pi_prod_aux μ T Ψ hΨmeas hΨL2
  have hboundint : Integrable bound P := by
    have h1 : MemLp (fun p : Fin T → Ω => |D p|) 2 P := hD.abs
    have h2 : MemLp (fun p : Fin T → Ω => (T : ℝ) * ∏ i, Ψ (p i)) 2 P := hΨprod.const_mul _
    exact h1.integrable_mul h2
  have hballabs : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) ε → |t| < ε := by
    intro t ht
    simpa [Real.dist_eq] using ht
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := bound) (s := Metric.ball (0:ℝ) ε) (Metric.ball_mem_nhds 0 hε)
    (Filter.Eventually.of_forall fun t => (hFmeas t).aestronglyMeasurable)
    (by rw [hF0]; exact hD.integrable one_le_two) hF'meas.aestronglyMeasurable
    ?hbnd hboundint ?hdiff
  · refine hkey.2.congr_deriv ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [hF', hL0]
  case hbnd =>
    filter_upwards with p
    intro t ht
    have habs := hballabs t ht
    rw [Real.norm_eq_abs, hF', hbound]
    simp only [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i)|
        ≤ ∑ i : Fin T, |(∏ j ∈ Finset.univ.erase i, L t (p j)) * L' t (p i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin T, ∏ j, Ψ (p j) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have h1 : |∏ j ∈ Finset.univ.erase i, L t (p j)| ≤ ∏ j ∈ Finset.univ.erase i, Ψ (p j) := by
            rw [Finset.abs_prod]
            exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
              (fun j _ => hLbound (p j) t habs)
          have h2 : |L' t (p i)| ≤ Ψ (p i) := hL'bound (p i) t habs
          have hnn : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, Ψ (p j) :=
            Finset.prod_nonneg fun j _ => le_trans zero_le_one (hΨ1 (p j))
          calc |∏ j ∈ Finset.univ.erase i, L t (p j)| * |L' t (p i)|
              ≤ (∏ j ∈ Finset.univ.erase i, Ψ (p j)) * Ψ (p i) := by
                exact mul_le_mul h1 h2 (abs_nonneg _) hnn
            _ = ∏ j, Ψ (p j) := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
      _ = (T : ℝ) * ∏ j, Ψ (p j) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  case hdiff =>
    filter_upwards with p
    intro t ht
    have habs := hballabs t ht
    have hprod : HasDerivAt (fun u : ℝ => ∏ i : Fin T, L u (p i))
        (∑ i : Fin T, (∏ j ∈ Finset.univ.erase i, L t (p j)) • L' t (p i)) t :=
      HasDerivAt.fun_finsetProd (f := fun i u => L u (p i)) (f' := fun i => L' t (p i))
        (fun i _ => hderiv (p i) t habs)
    have := hprod.const_mul (D p)
    refine this.congr_deriv ?_
    simp [hF', smul_eq_mul, Finset.mul_sum]

end Deriv

end Statistics

end

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (Ψ : Ω → ℝ)
    (hΨmeas : Measurable Ψ) (hΨ : MemLp Ψ 2 μ) :
    MemLp (fun p : Fin T → Ω => ∏ i, Ψ (p i)) 2 (Measure.pi fun _ : Fin T => μ) :=
  Statistics.memLp_two_pi_prod_aux μ T Ψ hΨmeas hΨ
