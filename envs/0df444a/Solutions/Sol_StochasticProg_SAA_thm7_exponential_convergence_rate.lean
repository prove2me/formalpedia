-- Prove2me | solution 1 for StochasticProg.SAA.thm7_exponential_convergence_rate
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:17:21.557691+00:00
-- url     : https://prove2.me/submissions/b8e6e029-2668-4705-83b7-b285d1d91f2c

import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace SAACounterexample

abbrev E := EuclideanSpace ℝ (Fin 1)
def point (s : Finset ℕ) : E := WithLp.toLp 2 (fun _ => (Encodable.encode s : ℝ) + 1)

theorem point_injective : Function.Injective point := by
  intro s t h
  have h' := congrArg (fun x : E => x 0) h
  change (Encodable.encode s : ℝ) + 1 = (Encodable.encode t : ℝ) + 1 at h'
  exact Encodable.encode_injective (by exact_mod_cast (add_right_cancel h'))

theorem point_ne_zero (s : Finset ℕ) : point s ≠ 0 := by
  intro h
  have h' := congrArg (fun x : E => x 0) h
  change (Encodable.encode s : ℝ) + 1 = 0 at h'
  have : (0 : ℝ) ≤ Encodable.encode s := Nat.cast_nonneg _
  linarith

theorem one_le_norm_point (s : Finset ℕ) : 1 ≤ ‖point s‖ := by
  have h := PiLp.norm_apply_le (point s) (0 : Fin 1)
  change ‖(Encodable.encode s : ℝ) + 1‖ ≤ ‖point s‖ at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  have : (0 : ℝ) ≤ Encodable.encode s := Nat.cast_nonneg _
  linarith

def X : Set E := insert 0 (Set.range point)
def cost (x : E) (t : ℕ) : ℝ :=
  if x = 0 then 0 else if ∃ s : Finset ℕ, point s = x ∧ t ∈ s then 0 else 1

@[simp] theorem cost_zero (t : ℕ) : cost 0 t = 0 := by simp [cost]
@[simp] theorem cost_point (s : Finset ℕ) (t : ℕ) :
    cost (point s) t = if t ∈ s then 0 else 1 := by
  have h : (∃ u : Finset ℕ, point u = point s ∧ t ∈ u) ↔ t ∈ s := by
    constructor
    · rintro ⟨u, hu, ht⟩
      exact point_injective hu ▸ ht
    · intro ht; exact ⟨s, rfl, ht⟩
  simp [cost, point_ne_zero, h]

theorem cost_nonneg (x : E) (t : ℕ) : 0 ≤ cost x t := by
  unfold cost; split_ifs <;> norm_num
theorem cost_bound (x : E) (t : ℕ) : |cost x t| ≤ 1 := by
  unfold cost; split_ifs <;> norm_num

def p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
def μ : Measure ℕ := geometricMeasure p
instance : IsProbabilityMeasure μ := by unfold μ; infer_instance
def P : Measure (ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ => μ)
instance : IsProbabilityMeasure P := by unfold P; infer_instance
def ξ (i : ℕ) (ω : ℕ → ℕ) : ℕ := ω i
theorem ξ_meas (i : ℕ) : Measurable (ξ i) := measurable_pi_apply i
theorem ξ_law (i : ℕ) : HasLaw (ξ i) μ P :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i).hasLaw
theorem ξ_indep : iIndepFun ξ P := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)
theorem ξ_ident (i : ℕ) : IdentDistrib (ξ i) (ξ 0) P P :=
  (ξ_law i).identDistrib (ξ_law 0)

theorem positive_integral_point (s : Finset ℕ) :
    0 < ∫ ω, cost (point s) (ξ 0 ω) ∂P := by
  rw [show (fun ω => cost (point s) (ξ 0 ω)) = cost (point s) ∘ ξ 0 from rfl,
    (ξ_law 0).integral_comp (measurable_of_countable _).aestronglyMeasurable]
  have hint : Integrable (cost (point s)) μ :=
    (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using cost_bound (point s) t))
  apply (integral_pos_iff_support_of_nonneg (cost_nonneg (point s)) hint).mpr
  let t := s.sup id + 1
  have ht : t ∉ s := by
    intro hm
    have := Finset.le_sup (f := id) hm
    simp only [id_eq] at this
    dsimp [t] at this
    omega
  have hsub : ({t} : Set ℕ) ⊆ Function.support (cost (point s)) := by
    intro u hu
    have : u = t := Set.mem_singleton_iff.mp hu
    subst u
    simp [Function.mem_support, ht]
  have hp0 : p ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  have hp1 : p ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  have hpos : 0 < μ {t} := by
    change 0 < geometricMeasure p {t}
    rw [geometricMeasure_singleton hp0]
    exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos hp0 hp1 t)
  exact hpos.trans_le (measure_mono hsub)

def samples (ν : ℕ) (ω : ℕ → ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin ν => ω i)
def xSAA (ν : ℕ) (ω : ℕ → ℕ) : E := point (samples ν ω)
def zSAA (_ : ℕ) (_ : ℕ → ℕ) : ℝ := 0

theorem xSAA_meas (ν : ℕ) : Measurable (xSAA ν) := by
  have h1 : Measurable (fun ω : ℕ → ℕ => fun i : Fin ν => ω i) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : ℕ))
  have h2 : Measurable (fun f : Fin ν → ℕ => point (Finset.univ.image f)) :=
    measurable_of_countable _
  exact h2.comp h1

theorem sample_cost_zero (ν : ℕ) (ω : ℕ → ℕ) (i : ℕ) (hi : i ∈ Finset.range ν) :
    cost (xSAA ν ω) (ξ i ω) = 0 := by
  have hm : ξ i ω ∈ samples ν ω := by
    apply Finset.mem_image.mpr
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
  simp [xSAA, hm]

theorem unique_optimum :
    Set.Subsingleton {x ∈ X | (∫ ω, cost x (ξ 0 ω) ∂P) = 0} := by
  have hz : ∀ x ∈ X, (∫ ω, cost x (ξ 0 ω) ∂P) = 0 → x = 0 := by
    intro x hx he
    rcases hx with hx | ⟨s, rfl⟩
    · exact hx
    · exact False.elim ((ne_of_gt (positive_integral_point s)) he)
  intro x hx y hy
  exact (hz x hx.1 hx.2).trans (hz y hy.1 hy.2).symm

end SAACounterexample

private theorem no_exponential_bound_for_probability_one :
    ¬ ∃ α > (0 : ℝ), ∃ β > (0 : ℝ),
      ∀ ν : ℕ, ν > 0 →
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal (α * Real.exp (-β * ν)) := by
  rintro ⟨α, hα, β, hβ, hbound⟩
  obtain ⟨ν, hν⟩ := exists_nat_gt (α / β + 1)
  have hνpos : 0 < ν := by
    have hdiv : 0 < α / β := div_pos hα hβ
    have : (0 : ℝ) < ν := by linarith
    exact_mod_cast this
  have hαν : α < β * (ν : ℝ) := by
    have hdivν : α / β < ν := by linarith
    have := (div_lt_iff₀ hβ).mp hdivν
    nlinarith
  have hexp : α < Real.exp (β * (ν : ℝ)) := by
    have := Real.add_one_le_exp (β * (ν : ℝ))
    linarith
  have hsmall : α * Real.exp (-β * (ν : ℝ)) < 1 := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr hexp
  have hlarge := ENNReal.one_le_ofReal.mp (hbound ν hνpos)
  linarith


theorem solution : ¬ (∀ {n : ℕ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → Ξ)
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (hgmeas : ∀ x ∈ X, Measurable (g x))
    (zStar : ℝ) (xStar : EuclideanSpace ℝ (Fin n))
    (hxStar : xStar ∈ X ∧ (∫ ω, g xStar (ξ 0 ω) ∂P) = zStar)
    (hzStar : ∀ x ∈ X, zStar ≤ ∫ ω, g x (ξ 0 ω) ∂P)
    (zSAA : ℕ → Ω → ℝ) (xSAA : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hSAA : ∀ ν ω, xSAA ν ω ∈ X ∧
      (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g (xSAA ν ω) (ξ i ω) = zSAA ν ω)
    (hSAA_opt : ∀ ν ω, ∀ x ∈ X, zSAA ν ω ≤ (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν, g x (ξ i ω))
    (a θ0 : ℝ) (ha : 0 < a) (hθ0 : 0 < θ0) (η : Ξ → ℝ)
    (hbound : ∀ x ∈ X, ∀ ξ' : Ξ, |g x ξ'| ≤ a * η ξ')
    (hmgf : ∀ θ ∈ Set.Icc (0 : ℝ) θ0, Integrable (fun ω => Real.exp (θ * η (ξ 0 ω))) P)
    (hzSAA_meas : ∀ ν, Measurable (zSAA ν)) (hxSAA_meas : ∀ ν, Measurable (xSAA ν))
    (ε : ℝ) (hε : 0 < ε),
    ∃ α > 0, ∃ β > 0,
      (∀ ν > 0, P {ω | ε ≤ |zSAA ν ω - zStar|} ≤ ENNReal.ofReal (α * Real.exp (-β * ν))) ∧
      ((Set.Subsingleton {x ∈ X | (∫ ω, g x (ξ 0 ω) ∂P) = zStar}) →
        ∀ ν ≥ 1, P {ω | ε ≤ ‖xSAA ν ω - xStar‖} ≤ ENNReal.ofReal (α * Real.exp (-β * ν))) ) := by
  intro h
  have hstar : (0 : SAACounterexample.E) ∈ SAACounterexample.X ∧
      (∫ ω, SAACounterexample.cost 0 (SAACounterexample.ξ 0 ω) ∂SAACounterexample.P) = 0 := by
    constructor
    · exact Set.mem_insert 0 _
    · simp
  have hlower : ∀ x ∈ SAACounterexample.X,
      (0 : ℝ) ≤ ∫ ω, SAACounterexample.cost x (SAACounterexample.ξ 0 ω)
        ∂SAACounterexample.P := by
    intro x _
    exact integral_nonneg (fun ω => SAACounterexample.cost_nonneg x _)
  have hsaa : ∀ ν ω, SAACounterexample.xSAA ν ω ∈ SAACounterexample.X ∧
      (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν,
        SAACounterexample.cost (SAACounterexample.xSAA ν ω) (SAACounterexample.ξ i ω) =
          SAACounterexample.zSAA ν ω := by
    intro ν ω
    constructor
    · exact Set.mem_insert_of_mem 0 (Set.mem_range_self (SAACounterexample.samples ν ω))
    · have hz : ∑ i ∈ Finset.range ν,
          SAACounterexample.cost (SAACounterexample.xSAA ν ω) (SAACounterexample.ξ i ω) = 0 :=
        Finset.sum_eq_zero (fun i hi => SAACounterexample.sample_cost_zero ν ω i hi)
      simp [hz, SAACounterexample.zSAA]
  have hopt : ∀ ν ω, ∀ x ∈ SAACounterexample.X,
      SAACounterexample.zSAA ν ω ≤ (ν : ℝ)⁻¹ * ∑ i ∈ Finset.range ν,
        SAACounterexample.cost x (SAACounterexample.ξ i ω) := by
    intro ν ω x _
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg ν))
      (Finset.sum_nonneg (fun i _ => SAACounterexample.cost_nonneg x _))
  obtain ⟨α, hα, β, hβ, _, hsol⟩ := @h 1 (ℕ → ℕ) ℕ inferInstance inferInstance
    SAACounterexample.X SAACounterexample.cost SAACounterexample.P inferInstance
    SAACounterexample.ξ SAACounterexample.ξ_indep SAACounterexample.ξ_ident
    (fun _ _ => measurable_of_countable _) 0 0 hstar hlower
    SAACounterexample.zSAA SAACounterexample.xSAA hsaa hopt
    1 1 (by norm_num) (by norm_num) (fun _ => 1)
    (fun x _ t => by simpa using SAACounterexample.cost_bound x t)
    (fun θ _ => by simpa using integrable_const (Real.exp θ))
    (fun _ => measurable_const) SAACounterexample.xSAA_meas 1 (by norm_num)
  apply no_exponential_bound_for_probability_one
  refine ⟨α, hα, β, hβ, ?_⟩
  intro ν hν
  have hb := hsol SAACounterexample.unique_optimum ν (by omega)
  have hevent : {ω : ℕ → ℕ | (1 : ℝ) ≤ ‖SAACounterexample.xSAA ν ω - 0‖} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    simpa [SAACounterexample.xSAA] using
      SAACounterexample.one_le_norm_point (SAACounterexample.samples ν ω)
  simpa only [hevent, measure_univ] using hb
