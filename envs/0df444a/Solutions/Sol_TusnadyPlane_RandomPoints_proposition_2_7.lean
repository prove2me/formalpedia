-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.proposition_2_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:53:34.983343+00:00
-- url     : https://prove2.me/submissions/9620bc3a-765d-4288-b077-24d1a1e4864f

import Mathlib
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Process.Adapted
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_TusnadyPlane_RandomPoints_scales
import Mathlib.MeasureTheory.Function.FactorsThrough
universe u

section
theorem ite_eq_left {α : Sort*} {p : Prop} {_ : Decidable p} {a b : α} (h : p) : (if p then a else b) = a :=
  if_pos h

theorem ite_eq_right {α : Sort*} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) : (if p then a else b) = b :=
  if_neg h
end

section
namespace Oscillation
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The normalized average on a finite set. -/
def finAvg (f : α → ℝ) : ℝ := (∑ x, f x) / Fintype.card α

lemma finAvg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : finAvg f = finAvg g := by
  unfold finAvg
  congr 1
  exact Finset.sum_congr rfl (fun x _ ↦ h x)

@[simp] lemma finAvg_const [Nonempty α] (c : ℝ) : finAvg (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finAvg, hc]

lemma finAvg_add (f g : α → ℝ) : finAvg (fun x ↦ f x + g x) = finAvg f + finAvg g := by
  simp [finAvg, Finset.sum_add_distrib, add_div]

lemma finAvg_sub (f g : α → ℝ) : finAvg (fun x ↦ f x - g x) = finAvg f - finAvg g := by
  simp [finAvg, Finset.sum_sub_distrib, sub_div]

lemma finAvg_mul_const (f : α → ℝ) (c : ℝ) : finAvg (fun x ↦ f x * c) = finAvg f * c := by
  simp only [finAvg, ← Finset.sum_mul]
  ring

lemma finAvg_const_mul (c : ℝ) (f : α → ℝ) : finAvg (fun x ↦ c * f x) = c * finAvg f := by
  simp only [finAvg, ← Finset.mul_sum]
  ring

lemma finAvg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : finAvg f ≤ finAvg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma finAvg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ finAvg f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ ↦ h x)) (Nat.cast_nonneg _)

lemma finAvg_equiv (e : α ≃ β) (f : β → ℝ) : finAvg (fun x ↦ f (e x)) = finAvg f := by
  rw [finAvg, finAvg, Fintype.card_congr e, e.sum_comp]

lemma finAvg_prod (f : α × β → ℝ) :
    finAvg f = finAvg (fun x : α ↦ finAvg (fun y : β ↦ f (x,y))) := by
  simp only [finAvg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma integral_uniform_eq_finAvg [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) : (∫ x, f x ∂(PMF.uniformOfFintype α).toMeasure) = finAvg f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finAvg]
  ring

lemma finAvg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    finAvg (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, finAvg (f i) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]

lemma finAvg_div_const (f : α → ℝ) (c : ℝ) :
    finAvg (fun x ↦ f x / c) = finAvg f / c := by
  simp only [finAvg, ← Finset.sum_div]
  ring

lemma finAvg_finAvg_comm (f : α → β → ℝ) :
    finAvg (fun x ↦ finAvg (f x)) = finAvg (fun y ↦ finAvg (fun x ↦ f x y)) := by
  simp only [finAvg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

end
end Oscillation
end

section
/-!
# Exponential bounds for the Riesz-product remainder

The lemmas below use genuine measure-theoretic expectations.  In particular,
the conditional result assumes zero conditional means and bounded increments,
and derives the exponential estimate rather than assuming it.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace Riesz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → ℝ}

section Conditional

variable [StandardBorelSpace Ω] [IsProbabilityMeasure μ]

end Conditional

end Riesz
end

section
/-! Bounded differences for actual finite independent coordinates. -/
namespace Oscillation
noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped NNReal
set_option maxHeartbeats 800000

variable {α : Type*} [Fintype α] [Nonempty α]

end
end Oscillation
end

section
/-!
# Iterating the coefficient Laplace bound across shapes

For nonnegative factors bounded by one, a conditional expectation bound at each
layer implies a product expectation bound. The factors may share all previously
exposed randomness; they are not assumed independent across layers.
-/

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

end Riesz

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

end Riesz
end

section
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end
end Oscillation
end

section
/-! One-directional accumulation of the actual finite conditional drift. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

end
end Oscillation
end

section
/-! The genuine finite endpoint-counting model and its oscillation potential. -/

namespace Oscillation

noncomputable section
open Finset

end
end Oscillation
end

section
/-!
# Point sets and probability interfaces for the direct Riesz proof

The basic point-set definitions and measure-theoretic proofs are extracted from
`Tusnady/Random.lean` and `Tusnady/PaperBasics.lean` in the audited v8 project
`review/tusnady-v8-verify-20261002-r_n7w581/Tusnady`.
This module imports only Mathlib; no random-walk, spectral-gap, or discrepancy
lower-bound result from the old development is used.
-/

open MeasureTheory Function Finset

namespace Riesz.PointSets

noncomputable abbrev μI : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure μI := ⟨by simp [μI, Real.volume_Icc]⟩

lemma unitSq_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1) = μI.prod μI := by
  rw [Set.Icc_prod_eq, Measure.volume_eq_prod, μI, Measure.prod_restrict]
  simp

lemma μI_compl_Ioc : μI (Set.Ioc 0 1)ᶜ = 0 := by
  rw [μI, Measure.restrict_apply measurableSet_Ioc.compl]
  refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and, not_le] at h1
  simp only [Set.mem_Icc] at h2
  simp only [Set.mem_singleton_iff]
  by_contra hx
  have := h1 (lt_of_le_of_ne h2.1 (Ne.symm hx))
  linarith [h2.2]

/-! ### From colorings of the plane and anchored rectangles to colorings of `X` -/

/-! ### Theorem 1.1 -/

/-! ### Random points -/


/-- The law of one uniform point of `[0,1]²` is a probability measure. -/
instance : IsProbabilityMeasure ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1)) := by
  rw [unitSq_eq]; infer_instance


/-- Law of independent uniform points in the unit square. -/
noncomputable abbrev unifPts (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin n => (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))

end Riesz.PointSets
end

section
/-!
# Cell averages as conditional expectations

A countable measurable cell index determines a partition sigma-algebra.  On
each positive-measure fiber, conditional expectation is exactly the integral
over that fiber divided by its measure. Null fibers are removed only on an
explicit almost-everywhere set; no positivity assumption is made on all cells.
-/

open MeasureTheory
open scoped ENNReal

namespace Riesz

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {mι : MeasurableSpace ι}
  {μ : Measure Ω} {p : Ω → ι} {f : Ω → ℝ}

/-- The normalized integral over the cell containing a point. -/
noncomputable def fiberMean (μ : Measure Ω) (p : Ω → ι) (f : Ω → ℝ) (x : Ω) : ℝ :=
  (∫ y in p ⁻¹' {p x}, f y ∂μ) / (μ (p ⁻¹' {p x})).toReal

/-- A function measurable for the cell-index sigma-algebra is constant on
each fiber, as an exact pointwise statement. -/
theorem measurable_comap_eq_of_index_eq {g : Ω → ℝ}
    (hg : Measurable[mι.comap p] g) {x y : Ω} (hxy : p x = p y) : g x = g y := by
  obtain ⟨s, _, hs⟩ := hg (measurableSet_singleton (g x))
  have hx : p x ∈ s := by
    have hx' : x ∈ g ⁻¹' {g x} := rfl
    rw [← hs] at hx'
    exact hx'
  have hy : y ∈ g ⁻¹' {g x} := by
    rw [← hs]
    change p y ∈ s
    rwa [← hxy]
  exact hy.symm

/-- The conditional expectation has the cell-average value at every point
whose fiber has positive measure. -/
theorem condExp_eq_fiberMean_of_measure_ne_zero [IsFiniteMeasure μ]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ)
    (x : Ω) (hcell : μ (p ⁻¹' {p x}) ≠ 0) :
    (μ[f | mι.comap p]) x = fiberMean μ p f x := by
  have hs : MeasurableSet (p ⁻¹' {p x}) := hp (measurableSet_singleton _)
  have hsc : MeasurableSet[mι.comap p] (p ⁻¹' {p x}) :=
    ⟨{p x}, measurableSet_singleton _, rfl⟩
  have hconstant : ∫ y in p ⁻¹' {p x}, (μ[f | mι.comap p]) y ∂μ =
      μ.real (p ⁻¹' {p x}) * (μ[f | mι.comap p]) x := by
    calc
      _ = ∫ _ in p ⁻¹' {p x}, (μ[f | mι.comap p]) x ∂μ := by
        apply setIntegral_congr_fun hs
        intro y hy
        exact measurable_comap_eq_of_index_eq stronglyMeasurable_condExp.measurable hy
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hμ : (μ (p ⁻¹' {p x})).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hcell, measure_ne_top _ _⟩
  apply (eq_div_iff hμ).mpr
  calc
    _ = ∫ y in p ⁻¹' {p x}, (μ[f | mι.comap p]) y ∂μ := by
      simpa [measureReal_def, mul_comm] using hconstant.symm
    _ = _ := setIntegral_condExp hp.comap_le hf hsc

/-- For a countable index, null fibers form a null set, even if some endpoints
or empty cells are assigned a separate index. -/
theorem ae_fiber_measure_ne_zero [Countable ι] :
    ∀ᵐ x ∂μ, μ (p ⁻¹' {p x}) ≠ 0 := by
  have hi (i : ι) : ∀ᵐ x ∂μ, p x = i → μ (p ⁻¹' {i}) ≠ 0 := by
    by_cases hz : μ (p ⁻¹' {i}) = 0
    · have havoid : ∀ᵐ x ∂μ, p x ≠ i := by
        simpa only [ae_iff, not_not, Set.preimage, Set.mem_singleton_iff] using hz
      filter_upwards [havoid] with x hx heq
      exact (hx heq).elim
    · exact Filter.Eventually.of_forall fun _ _ ↦ hz
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx (p x) rfl

/-- Conditional expectation for any countable measurable partition is the
normalized integral on its cells, with zero-measure cells handled a.e. -/
theorem condExp_ae_eq_fiberMean [IsFiniteMeasure μ] [Countable ι]
    [MeasurableSingletonClass ι] (hp : Measurable p) (hf : Integrable f μ) :
    μ[f | mι.comap p] =ᵐ[μ] fiberMean μ p f := by
  filter_upwards [ae_fiber_measure_ne_zero (μ := μ) (p := p)] with x hx
  exact condExp_eq_fiberMean_of_measure_ne_zero hp hf x hx

end Riesz

namespace Riesz

open PointSets

/-- Right-closed grid cells. The point zero lies in a separate null fiber
under the uniform measure on the unit interval. -/
noncomputable def gridIndex (n : ℕ) (x : ℝ) : ℤ := ⌈(n : ℝ) * x⌉ - 1

def gridCell (n : ℕ) (k : ℤ) : Set ℝ :=
  Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)

noncomputable def gridMean (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  n * ∫ y in gridCell n (gridIndex n x), f y

noncomputable abbrev gridSigma (n : ℕ) : MeasurableSpace ℝ :=
  (inferInstance : MeasurableSpace ℤ).comap (gridIndex n)

theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) := by
  exact ((measurable_const.mul measurable_id).ceil.sub_const 1)

theorem gridIndex_fiber (n : ℕ) (hn : 0 < n) (k : ℤ) :
    gridIndex n ⁻¹' {k} = gridCell n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, gridIndex, sub_eq_iff_eq_add,
    Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right,
    gridCell, Set.mem_Ioc, div_lt_iff₀ hn', le_div_iff₀ hn', mul_comm]

theorem gridCell_subset_unit (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : (0 : ℝ) ≤ k) (hkn : (k : ℝ) + 1 ≤ n) :
    gridCell n k ⊆ Set.Icc 0 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rintro x ⟨hx0, hx1⟩
  constructor
  · exact (div_nonneg hk hn'.le).trans hx0.le
  · exact hx1.trans ((div_le_one hn').mpr hkn)

theorem gridCell_measure (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : (0 : ℝ) ≤ k) (hkn : (k : ℝ) + 1 ≤ n) :
    μI (gridCell n k) = ENNReal.ofReal (1 / (n : ℝ)) := by
  rw [μI, Measure.restrict_eq_self _ (gridCell_subset_unit n hn k hk hkn),
    gridCell, Real.volume_Ioc]
  congr 1
  ring

theorem gridIndex_bounds (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    (0 : ℝ) ≤ gridIndex n x ∧ (gridIndex n x : ℝ) + 1 ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (1 : ℤ) ≤ ⌈(n : ℝ) * x⌉ :=
    Int.one_le_ceil_iff.mpr (mul_pos hn' hx.1)
  have hhi : ⌈(n : ℝ) * x⌉ ≤ (n : ℤ) := by
    apply Int.ceil_le.mpr
    simpa using mul_le_of_le_one_right hn'.le hx.2
  constructor
  · exact_mod_cast (show (0 : ℤ) ≤ gridIndex n x by unfold gridIndex; omega)
  · have hhi' : (⌈(n : ℝ) * x⌉ : ℝ) ≤ n := by exact_mod_cast hhi
    simpa [gridIndex] using hhi'

theorem fiberMean_gridIndex_eq_gridMean (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    fiberMean μI (gridIndex n) f x = gridMean f n x := by
  obtain ⟨hk, hkn⟩ := gridIndex_bounds n hn hx
  have hsub := gridCell_subset_unit n hn (gridIndex n x) hk hkn
  unfold fiberMean gridMean
  rw [gridIndex_fiber n hn, gridCell_measure n hn _ hk hkn,
    ENNReal.toReal_ofReal (by positivity)]
  have hint : (∫ y in gridCell n (gridIndex n x), f y ∂μI) =
      ∫ y in gridCell n (gridIndex n x), f y := by
    rw [μI, Measure.restrict_restrict_of_subset hsub]
  rw [hint]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual uniform-grid average is conditional expectation on the
sigma-algebra generated by its cell index. The endpoint zero is excluded by
the already proved null-measure endpoint fact, not a pointwise convention. -/
theorem condExp_ae_eq_gridMean (n : ℕ) (hn : 0 < n) {f : ℝ → ℝ}
    (hf : Integrable f μI) : μI[f | gridSigma n] =ᵐ[μI] gridMean f n := by
  have hcell := condExp_ae_eq_fiberMean (measurable_gridIndex n) hf
  have hunit : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 := by
    exact ae_iff.mpr μI_compl_Ioc
  filter_upwards [hcell, hunit] with x hx hxunit
  exact hx.trans (fiberMean_gridIndex_eq_gridMean n hn f hxunit)

end Riesz
end

section
/-!
# The one-dimensional profile used in the direct Riesz proof

`profile` is the primitive `w` from Section 2 of the manuscript.  It is extended by
zero outside the unit interval.  The lemmas in this file establish its actual
pointwise and integral properties; they are not hypotheses of a surrogate model.
-/

namespace Riesz

noncomputable section

end
end Riesz

namespace Riesz
noncomputable section
open Finset

end
end Riesz

namespace Riesz
noncomputable section

end
end Riesz
end

section
/-!
# Rare-set occupancy under genuine iid sampling

The probability measure is `Measure.pi (fun _ : Fin n => μ)`. No independence
or occupancy conclusion is postulated: product-event probabilities follow from
`Measure.pi_pi_finset`, and all exceptional-set choices are union bounded.
-/

namespace Riesz.Occupancy

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [MeasurableSpace α]

open PointSets

/-- A finite cell index for the actual uniform interval partition. The choice
outside `(0,1]` is immaterial because that set is null under `μI`. -/
noncomputable def finiteGridIndex (m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  if hx : x ∈ Set.Ioc (0 : ℝ) 1 then
    ⟨(gridIndex m x).toNat, by
      obtain ⟨hk, hk'⟩ := gridIndex_bounds m hm hx
      have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
      have hk1 : gridIndex m x < (m : ℤ) := by
        exact_mod_cast (show (gridIndex m x : ℝ) < m by linarith)
      omega⟩
  else ⟨0, hm⟩

lemma finiteGridIndex_eq {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ((finiteGridIndex m hm x : ℕ) : ℤ) = gridIndex m x := by
  have hk := (gridIndex_bounds m hm hx).1
  have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
  simp [finiteGridIndex, hx, Int.toNat_of_nonneg hk0]

lemma finiteGridIndex_mass (m : ℕ) (hm : 0 < m) (j : Fin m) :
    μI {x | finiteGridIndex m hm x = j} ≤ ENNReal.ofReal (1 / (m : ℝ)) := by
  have hsub : {x | finiteGridIndex m hm x = j} ⊆
      gridCell m (j : ℤ) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ := by
    intro x hx
    by_cases hxunit : x ∈ Set.Ioc (0 : ℝ) 1
    · left
      have heq := finiteGridIndex_eq hm hxunit
      rw [show finiteGridIndex m hm x = j from hx] at heq
      rw [← gridIndex_fiber m hm (j : ℤ)]
      exact heq.symm
    · exact Or.inr hxunit
  calc
    μI {x | finiteGridIndex m hm x = j} ≤ μI (gridCell m (j : ℤ) ∪ (Set.Ioc (0 : ℝ) 1)ᶜ) :=
      measure_mono hsub
    _ ≤ μI (gridCell m (j : ℤ)) + μI (Set.Ioc (0 : ℝ) 1)ᶜ := measure_union_le _ _
    _ = ENNReal.ofReal (1 / (m : ℝ)) := by
      rw [μI_compl_Ioc, add_zero, gridCell_measure m hm]
      · positivity
      · exact_mod_cast j.isLt

end Riesz.Occupancy
end

section
/-!
# Finite moment and Laplace bounds

The conditional distribution in the one-rectangle argument is finite: after the
old digits and vertical weights are fixed, the new horizontal digits range over
finitely many possibilities.  The theorems below apply to arbitrary finite
probability weights, not just the uniform distribution.
-/

namespace Riesz.Moments

open scoped BigOperators

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

variable {Ω : Type*} [Fintype Ω]

noncomputable def expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * X ω

@[simp] lemma expectation_const (μ : FiniteLaw Ω) (a : ℝ) :
    expectation μ (fun _ ↦ a) = a := by
  simp only [expectation, ← Finset.sum_mul, μ.total, one_mul]

end Riesz.Moments
end

section
/-!
# The finite law of one dyadically averaged profile

The support `Fin 4 × Fin m` is the first two horizontal bits followed by the
remaining bits (`m = 2^(L-2)`).  `profile_cell_average` identifies each value
below with the integral average of the actual continuous profile on its cell.
-/

namespace Riesz
noncomputable section
open Finset Moments

end
end Riesz
end

section
/-!
# Refinement of the actual uniform grids

The right-closed cell convention is preserved at every level, including at
cell boundaries. Thus refinement holds pointwise, before discarding null
endpoints in the conditional-average identities.
-/

open MeasureTheory

namespace Riesz

/-- The coarse index is integer division of the fine index. -/
theorem gridIndex_mul_ediv (n m : ℕ) (hm : 0 < m) (x : ℝ) :
    gridIndex (n * m) x / (m : ℤ) = gridIndex n x := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc := Int.ceil_eq_iff.mp (rfl : ⌈(n : ℝ) * x⌉ = ⌈(n : ℝ) * x⌉)
  apply le_antisymm
  · have hb : ⌈((n * m : ℕ) : ℝ) * x⌉ ≤ ⌈(n : ℝ) * x⌉ * (m : ℤ) := by
      apply Int.ceil_le.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hc.2 hmr.le]
    have hb' : gridIndex (n * m) x < (gridIndex n x + 1) * (m : ℤ) := by
      simpa only [gridIndex, sub_add_cancel] using
        (show ⌈((n * m : ℕ) : ℝ) * x⌉ - 1 < ⌈(n : ℝ) * x⌉ * (m : ℤ) by omega)
    have := (Int.ediv_lt_iff_lt_mul hmz).mpr hb'
    omega
  · apply (Int.le_ediv_iff_mul_le hmz).mpr
    have hb : (⌈(n : ℝ) * x⌉ - 1) * (m : ℤ) <
        ⌈((n * m : ℕ) : ℝ) * x⌉ := by
      apply Int.lt_ceil.mpr
      push_cast
      nlinarith [mul_lt_mul_of_pos_right hc.1 hmr]
    simp only [gridIndex]
    omega

/-- Every coarse-grid event is a fine-grid event. -/
theorem gridSigma_le_mul (n m : ℕ) (hm : 0 < m) :
    gridSigma n ≤ gridSigma (n * m) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (fun k : ℤ ↦ k / (m : ℤ))
    (measurable_of_countable _)
  funext x
  exact (gridIndex_mul_ediv n m hm x).symm

/-- Refinement for arbitrary divisible positive grid sizes. -/
theorem gridSigma_mono_of_dvd {n m : ℕ} (hm : 0 < m) (hnm : n ∣ m) :
    gridSigma n ≤ gridSigma m := by
  obtain ⟨k, rfl⟩ := hnm
  exact gridSigma_le_mul n k (Nat.pos_of_mul_pos_left hm)

/-- The sigma-algebras of dyadic grids form an increasing sequence. -/
theorem dyadic_gridSigma_mono : Monotone (fun r : ℕ ↦ gridSigma (2 ^ r)) := by
  intro r s hrs
  exact gridSigma_mono_of_dvd (pow_pos (by norm_num) _) (Nat.pow_dvd_pow 2 hrs)

/-- The filtration generated by right-closed dyadic cells on the real line. -/
noncomputable def dyadicFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq r := gridSigma (2 ^ r)
  mono' := dyadic_gridSigma_mono
  le' r := (measurable_gridIndex (2 ^ r)).comap_le

@[simp] theorem dyadicFiltration_apply (r : ℕ) :
    dyadicFiltration r = gridSigma (2 ^ r) := rfl

/-- Every `L`th dyadic level is again a filtration. -/
noncomputable def spacedDyadicFiltration (L : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq j := gridSigma (2 ^ (j * L))
  mono' := fun _ _ hij ↦ dyadic_gridSigma_mono (Nat.mul_le_mul_right L hij)
  le' j := (measurable_gridIndex (2 ^ (j * L))).comap_le

@[simp] theorem spacedDyadicFiltration_apply (L j : ℕ) :
    spacedDyadicFiltration L j = gridSigma (2 ^ (j * L)) := rfl

/-- Every point belongs to the cell selected by its index. -/
theorem mem_gridCell_gridIndex (n : ℕ) (hn : 0 < n) (x : ℝ) :
    x ∈ gridCell n (gridIndex n x) := by
  rw [← gridIndex_fiber n hn]
  simp

open PointSets

end Riesz
end

section
/-!
# The distribution of the actual finite grid index

These identities connect uniform real samples with the finite laws used by the
moment argument. The cell endpoints use the same right-closed convention as
`CellAverages`; the exceptional complement of `(0,1]` is handled by its null measure.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal

lemma measurable_finiteGridIndex (m : ℕ) (hm : 0 < m) :
    Measurable (finiteGridIndex m hm) := by
  let g : ℤ → Fin m := fun k => ⟨k.toNat % m, Nat.mod_lt _ hm⟩
  have heq : finiteGridIndex m hm = fun x =>
      if x ∈ Set.Ioc (0 : ℝ) 1 then g (gridIndex m x) else ⟨0, hm⟩ := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp only [finiteGridIndex, hx, dite_true, ite_true]
      apply Fin.ext
      dsimp [g]
      rw [Nat.mod_eq_of_lt]
      obtain ⟨hk, hkn⟩ := gridIndex_bounds m hm hx
      have hk0 : (0 : ℤ) ≤ gridIndex m x := by exact_mod_cast hk
      have hk1 : gridIndex m x < (m : ℤ) := by
        exact_mod_cast (show (gridIndex m x : ℝ) < m by linarith)
      omega
    · simp [finiteGridIndex, hx]
  rw [heq]
  exact Measurable.ite measurableSet_Ioc
    ((measurable_of_countable g).comp (measurable_gridIndex m)) measurable_const

lemma finiteGridIndex_fiber_mass (m : ℕ) (hm : 0 < m) (j : Fin m) :
    μI {x | finiteGridIndex m hm x = j} = ENNReal.ofReal (1 / (m : ℝ)) := by
  apply le_antisymm (finiteGridIndex_mass m hm j)
  have hsub : gridCell m (j : ℤ) ⊆ {x | finiteGridIndex m hm x = j} := by
    intro x hx
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hxunit : x ∈ Set.Ioc (0 : ℝ) 1 := by
      refine ⟨lt_of_le_of_lt (div_nonneg (by positivity) hm'.le) hx.1, ?_⟩
      apply hx.2.trans
      apply (div_le_one hm').mpr
      exact_mod_cast j.isLt
    have hi := finiteGridIndex_eq hm hxunit
    have hj : gridIndex m x = (j : ℤ) := by
      rw [← gridIndex_fiber m hm] at hx
      exact hx
    apply Fin.ext
    exact_mod_cast hi.trans hj
  have hh := measure_mono (μ := μI) hsub
  rw [gridCell_measure m hm _ (by positivity) (by exact_mod_cast j.isLt)] at hh
  exact hh

/-- The expectation of any function of the actual grid cell is its uniform
finite average. This is an equality of Lebesgue integrals, not a distributional assumption. -/
theorem integral_finiteGridIndex (m : ℕ) (hm : 0 < m) (f : Fin m → ℝ) :
    (∫ x, f (finiteGridIndex m hm x) ∂μI) = (∑ j, f j) / m := by
  have hi := measurable_finiteGridIndex m hm
  rw [← integral_map hi.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp_rw [measureReal_def, Measure.map_apply hi (measurableSet_singleton _),
    show ∀ j : Fin m, finiteGridIndex m hm ⁻¹' {j} = {x | finiteGridIndex m hm x = j} from
      fun _ => rfl,
    finiteGridIndex_fiber_mass, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (m : ℝ)),
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring


/-- The fresh block index after the `n`-cell coarse index has been exposed.
Its value depends on the position rescaled inside that actual coarse cell. -/
def freshGridIndex (n m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  finiteGridIndex m hm ((n : ℝ) * x - gridIndex n x)

lemma measurable_freshGridIndex (n m : ℕ) (hm : 0 < m) :
    Measurable (freshGridIndex n m hm) := by
  exact (measurable_finiteGridIndex m hm).comp
    ((measurable_const.mul measurable_id).sub
      ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp (measurable_gridIndex n)))

lemma integrable_freshGridFunction (n m : ℕ) (hm : 0 < m) (f : Fin m → ℝ) :
    Integrable (fun x => f (freshGridIndex n m hm x)) μI := by
  apply Integrable.of_bound
    ((measurable_of_countable f).comp (measurable_freshGridIndex n m hm)).aestronglyMeasurable
    (∑ j, |f j|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ _)

/-- Every coarse cell contains the same uniform distribution of fresh indices.
This calculation is pointwise in the coarse cell and includes grid boundaries. -/
theorem gridMean_freshGridIndex (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : Fin m → ℝ) (x : ℝ) :
    gridMean (fun y => f (freshGridIndex n m hm y)) n x = (∑ j, f j) / m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let k : ℤ := gridIndex n x
  have hab : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
    gcongr
    exact le_add_of_nonneg_right (by norm_num)
  have hcell : (∫ y in gridCell n k, f (freshGridIndex n m hm y)) =
      ∫ y in gridCell n k, f (finiteGridIndex m hm ((n : ℝ) * y - k)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    have hk : gridIndex n y = k := by
      change y ∈ gridCell n k at hy
      rw [← gridIndex_fiber n hn] at hy
      exact hy
    simp only [freshGridIndex, hk]
  unfold gridMean
  change (n : ℝ) * (∫ y in gridCell n k, f (freshGridIndex n m hm y)) = _
  rw [hcell]
  unfold gridCell
  rw [← intervalIntegral.integral_of_le hab]
  simp_rw [sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_mul_add (fun y => f (finiteGridIndex m hm y)) hn'.ne' (-(k : ℝ))]
  have hleft : (n : ℝ) * ((k : ℝ) / n) + -(k : ℝ) = 0 := by field_simp; ring
  have hright : (n : ℝ) * (((k : ℝ) + 1) / n) + -(k : ℝ) = 1 := by field_simp; ring
  rw [hleft, hright, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hint : (∫ y in Set.Ioc (0 : ℝ) 1, f (finiteGridIndex m hm y)) =
      ∫ y, f (finiteGridIndex m hm y) ∂μI := by
    rw [μI, ← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [hint, integral_finiteGridIndex]

/-- The newly exposed block is conditionally uniform given the genuine coarse
grid sigma-algebra. The average is proved, not assumed as conditional independence. -/
theorem condExp_freshGridIndex (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : Fin m → ℝ) :
    μI[(fun x => f (freshGridIndex n m hm x)) | gridSigma n] =ᵐ[μI]
      (fun _ => (∑ j, f j) / m) := by
  refine (condExp_ae_eq_gridMean n hn (integrable_freshGridFunction n m hm f)).trans ?_
  exact Filter.Eventually.of_forall (gridMean_freshGridIndex n m hn hm f)


lemma coarseLocalCoordinate_mem (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (n : ℝ) * x - gridIndex n x ∈ Set.Ioc (0 : ℝ) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx := mem_gridCell_gridIndex n hn x
  change (gridIndex n x : ℝ) / n < x ∧ x ≤ ((gridIndex n x : ℝ) + 1) / n at hx
  rw [div_lt_iff₀ hn', le_div_iff₀ hn'] at hx
  constructor <;> nlinarith [hx.1, hx.2]

/-- The fresh block is exactly the remainder of the refined cell index. -/
theorem freshGridIndex_eq_emod (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (x : ℝ) :
    ((freshGridIndex n m hm x : ℕ) : ℤ) = gridIndex (n * m) x % (m : ℤ) := by
  rw [freshGridIndex, finiteGridIndex_eq hm (coarseLocalCoordinate_mem n hn x)]
  have hshift : (m : ℝ) * ((n : ℝ) * x - gridIndex n x) =
      ((n * m : ℕ) : ℝ) * x - (((m : ℤ) * gridIndex n x : ℤ) : ℝ) := by
    push_cast
    ring
  unfold gridIndex at hshift ⊢
  rw [hshift, Int.ceil_sub_intCast]
  change ⌈((n * m : ℕ) : ℝ) * x⌉ - (m : ℤ) * gridIndex n x - 1 =
    gridIndex (n * m) x % (m : ℤ)
  rw [Int.emod_def, gridIndex_mul_ediv n m hm]
  unfold gridIndex
  ring


end
end Riesz
end

section
/-!
# Conditional fresh blocks for independent real samples

The coarse cells are the actual grid cells of all sample coordinates. The
product identities derive conditional independence from the product measure;
no independence between different shape levels is assumed.
-/

namespace Riesz
noncomputable section
open MeasureTheory PointSets Occupancy
open scoped ENNReal

/-- Normalized averages of coordinate products factor over the actual product
partition, including zero-measure fibers. -/
theorem fiberMean_pi_product {ι α κ : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p : α → κ) (f : ι → α → ℝ) (x : ι → α) :
    fiberMean (Measure.pi (fun _ : ι => μ)) (fun y i => p (y i))
      (fun y => ∏ i, f i (y i)) x = ∏ i, fiberMean μ p (f i) (x i) := by
  have hcell : (fun y : ι → α => fun i => p (y i)) ⁻¹' {fun i => p (x i)} =
      Set.univ.pi (fun i => p ⁻¹' {p (x i)}) := by
    ext y
    simp [funext_iff]
  unfold fiberMean
  rw [hcell, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_div_distrib]

/-- The information in the first `k` horizontal cells for every sample point. -/
def sampleGridIndex (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => gridIndex k (x i)

abbrev sampleGridSigma (n k : ℕ) : MeasurableSpace (Fin n → ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → ℤ)).comap (sampleGridIndex n k)

lemma measurable_sampleGridIndex (n k : ℕ) : Measurable (sampleGridIndex n k) := by
  exact measurable_pi_iff.mpr (fun i => (measurable_gridIndex k).comp (measurable_pi_apply i))

/-- A product of functions of fresh blocks has the product of their uniform
averages, even after every coarse sample cell has been revealed. -/
theorem condExp_freshGrid_product (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (f : Fin n → Fin m → ℝ) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => ∏ i, f i (freshGridIndex k m hm (x i))) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)] (fun _ => ∏ i, (∑ a, f i a) / m) := by
  let μ := Measure.pi (fun _ : Fin n => μI)
  have hf (i : Fin n) : Integrable (fun x => f i (freshGridIndex k m hm x)) μI :=
    integrable_freshGridFunction k m hm (f i)
  have hi (i : Fin n) : ∀ᵐ x ∂μI,
      fiberMean μI (gridIndex k) (fun y => f i (freshGridIndex k m hm y)) x =
        (∑ a, f i a) / m :=
    (condExp_ae_eq_fiberMean (measurable_gridIndex k) (hf i)).symm.trans
      (condExp_freshGridIndex k m hk hm (f i))
  have hiall : ∀ᵐ x ∂μ, ∀ i : Fin n,
      fiberMean μI (gridIndex k) (fun y => f i (freshGridIndex k m hm y)) (x i) =
        (∑ a, f i a) / m := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI) (i := i) (hi i)
  have hcond := condExp_ae_eq_fiberMean (μ := μ) (measurable_sampleGridIndex n k)
    (Integrable.fintype_prod hf)
  filter_upwards [hcond, hiall] with x hx hxi
  rw [hx]
  change fiberMean μ (fun y i => gridIndex k (y i))
    (fun y => ∏ i, f i (freshGridIndex k m hm (y i))) x = _
  rw [fiberMean_pi_product μI (gridIndex k) (fun i y => f i (freshGridIndex k m hm y)) x]
  exact Finset.prod_congr rfl (fun i _ => hxi i)

lemma finiteFunction_delta_expansion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (H : (ι → α) → ℝ) (a : ι → α) :
    H a = ∑ b : ι → α, H b * ∏ i, (if a i = b i then (1 : ℝ) else 0) := by
  classical
  have hb (b : ι → α) : (∏ i, (if a i = b i then (1 : ℝ) else 0)) =
      if a = b then 1 else 0 := by
    simp only [Fintype.prod_boole, ← funext_iff]
  simp_rw [hb, mul_ite, mul_one, mul_zero]
  simp

/-- An arbitrary statistic of all fresh digit blocks has the uniform product
law conditionally on all old blocks. This is stronger than pairwise independence. -/
theorem condExp_freshGrid_vector (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → Fin m) → ℝ) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => H (fun i => freshGridIndex k m hm (x i))) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)] (fun _ => (∑ a, H a) / (m : ℝ) ^ n) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => μI)
  let δ : (Fin n → Fin m) → (Fin n → ℝ) → ℝ := fun b x =>
    ∏ i, if freshGridIndex k m hm (x i) = b i then 1 else 0
  have hδ (b : Fin n → Fin m) : Integrable (δ b) μ :=
    Integrable.fintype_prod (fun i =>
      integrable_freshGridFunction k m hm (fun a => if a = b i then 1 else 0))
  have hmean (b : Fin n → Fin m) : μ[δ b | sampleGridSigma n k] =ᵐ[μ]
      (fun _ => 1 / (m : ℝ) ^ n) := by
    have h := condExp_freshGrid_product n k m hk hm
      (fun i a => if a = b i then 1 else 0)
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_div_pow] using h
  have hscaled (b : Fin n → Fin m) :
      μ[(fun x => H b * δ b x) | sampleGridSigma n k] =ᵐ[μ]
        (fun _ => H b / (m : ℝ) ^ n) := by
    have hsm := condExp_smul (μ := μ) (H b) (δ b) (sampleGridSigma n k)
    filter_upwards [hsm, hmean b] with x hx hy
    change μ[H b • δ b | sampleGridSigma n k] x = _
    simpa only [Pi.smul_apply, smul_eq_mul, hy, mul_one_div] using hx
  have heq : (fun x => H (fun i => freshGridIndex k m hm (x i))) =
      ∑ b : Fin n → Fin m, (fun x => H b * δ b x) := by
    funext x
    simpa only [Finset.sum_apply, δ] using
      finiteFunction_delta_expansion H (fun i => freshGridIndex k m hm (x i))
  rw [heq]
  have hsum := condExp_finsetSum (μ := μ)
    (s := Finset.univ) (fun b _ => (hδ b).const_mul (H b)) (sampleGridSigma n k)
  filter_upwards [hsum, ae_all_iff.mpr hscaled] with x hx hxs
  simp only [Finset.sum_apply] at hx
  rw [hx]
  simp_rw [hxs]
  rw [Finset.sum_div]


/-- The vector of freshly exposed block indices. -/
def sampleFreshIndex (n k m : ℕ) (hm : 0 < m) (x : Fin n → ℝ) : Fin n → Fin m :=
  fun i => freshGridIndex k m hm (x i)

lemma measurable_sampleFreshIndex (n k m : ℕ) (hm : 0 < m) :
    Measurable (sampleFreshIndex n k m hm) := by
  exact measurable_pi_iff.mpr
    (fun i => (measurable_freshGridIndex k m hm).comp (measurable_pi_apply i))

lemma integrable_sampleFreshFunction (n k m : ℕ) (hm : 0 < m)
    (H : (Fin n → Fin m) → ℝ) :
    Integrable (fun x => H (sampleFreshIndex n k m hm x)) (Measure.pi (fun _ : Fin n => μI)) := by
  apply Integrable.of_bound
    ((measurable_of_countable H).comp (measurable_sampleFreshIndex n k m hm)).aestronglyMeasurable
    (∑ a, |H a|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun a _ => abs_nonneg (H a)) (Finset.mem_univ _)

/-- The statistic may depend arbitrarily on the revealed coarse sample cells.
Its fresh variables still have the uniform product law in each such cell. -/
theorem condExp_freshGrid_with_past (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : Integrable (fun x => H (sampleGridIndex n k x) (sampleFreshIndex n k m hm x))
      (Measure.pi (fun _ : Fin n => μI))) :
    (Measure.pi (fun _ : Fin n => μI))[
      (fun x => H (sampleGridIndex n k x) (sampleFreshIndex n k m hm x)) | sampleGridSigma n k] =ᵐ[
        Measure.pi (fun _ : Fin n => μI)]
      (fun x => (∑ a, H (sampleGridIndex n k x) a) / (m : ℝ) ^ n) := by
  let μ := Measure.pi (fun _ : Fin n => μI)
  let p := sampleGridIndex n k
  let q := sampleFreshIndex n k m hm
  have hp : Measurable p := measurable_sampleGridIndex n k
  have hf (b : Fin n → ℤ) : Integrable (fun x => H b (q x)) μ :=
    integrable_sampleFreshFunction n k m hm (H b)
  have hfixed (b : Fin n → ℤ) : ∀ᵐ x ∂μ,
      fiberMean μ p (fun y => H b (q y)) x = (∑ a, H b a) / (m : ℝ) ^ n :=
    (condExp_ae_eq_fiberMean hp (hf b)).symm.trans
      (condExp_freshGrid_vector n k m hk hm (H b))
  have hbase := condExp_ae_eq_fiberMean hp hH
  filter_upwards [hbase, ae_all_iff.mpr hfixed] with x hx hxf
  rw [hx]
  change fiberMean μ p (fun y => H (p y) (q y)) x = _
  calc
    fiberMean μ p (fun y => H (p y) (q y)) x =
        fiberMean μ p (fun y => H (p x) (q y)) x := by
      unfold fiberMean
      congr 1
      apply setIntegral_congr_fun (hp (measurableSet_singleton _))
      intro y hy
      change p y = p x at hy
      change H (p y) (q y) = H (p x) (q y)
      rw [hy]
    _ = _ := hxf (p x)


lemma sampleGridSigma_le_mul (n k m : ℕ) (hm : 0 < m) :
    sampleGridSigma n k ≤ sampleGridSigma n (k * m) := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun b : Fin n → ℤ => fun i => b i / (m : ℤ)) (measurable_of_countable _)
  funext x i
  exact (gridIndex_mul_ediv k m hm (x i)).symm


end
end Riesz
end

section
/-!
# Taking the finite union over every coloring

This file connects the fixed-coloring probability estimate to the actual bad
event for arbitrary index colorings. It does not assume that the coloring was
chosen independently of the point set.
-/

namespace Riesz.PointSets
noncomputable section
open MeasureTheory Finset
open scoped ENNReal

end
end Riesz.PointSets
end

section
/-! The finite endpoint model is realized by genuine uniform real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
open scoped BigOperators

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset MeasureTheory

end
end Oscillation
end

section
/-! Actual truncated base-b stages on iid horizontal real coordinates. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Riesz Riesz.PointSets

lemma sampleGridSigma_mono_pow (n b : ℕ) (hb : 0 < b) :
    Monotone (fun j ↦ sampleGridSigma n (b ^ j)) := by
  intro i j hij
  change sampleGridSigma n (b^i) ≤ sampleGridSigma n (b^j)
  have he : b ^ j = b ^ i * b ^ (j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [he]
  exact sampleGridSigma_le_mul n (b^i) (b^(j-i)) (pow_pos hb _)

def stageFiltration (n b h : ℕ) (hb : 0 < b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq j := sampleGridSigma n (b ^ min j h)
  mono' := fun _i _j hij ↦ sampleGridSigma_mono_pow n b hb (min_le_min_right h hij)
  le' j := (measurable_sampleGridIndex n (b ^ min j h)).comap_le

@[simp] lemma stageFiltration_apply (n b h : ℕ) (hb : 0 < b) (j : ℕ) :
    stageFiltration n b h hb j = sampleGridSigma n (b ^ min j h) := rfl

end
end Oscillation
end

section
namespace Riesz.Moments

open scoped BigOperators

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]


/-- The sample space of `n` genuinely independent draws, built as an iterated product. -/
def SampleSpace (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => SampleSpace Ω n × Ω

instance sampleSpaceFintype (Ω : Type*) [Fintype Ω] (n : ℕ) :
    Fintype (SampleSpace Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance

end Riesz.Moments
end

section
/-!
# From recursive independent samples to finite vectors

The weighted-moment proof uses an iterated binary product sample space. This
module identifies it with ordinary vectors and derives the normalized finite
sum needed by the conditional fresh-digit law. No moment or Laplace conclusion
is introduced as an assumption.
-/

namespace Riesz.Moments

open scoped BigOperators


/-- The recursive sample space is exactly the space of length-`n` vectors. -/
noncomputable def sampleSpaceEquiv (Ω : Type u) : (n : ℕ) → SampleSpace Ω n ≃ (Fin n → Ω)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    ((Equiv.prodCongr (sampleSpaceEquiv Ω n) (Equiv.refl Ω)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))

@[simp] lemma sampleSpaceEquiv_castSucc (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1))
    (i : Fin n) :
    sampleSpaceEquiv Ω (n + 1) ω i.castSucc = sampleSpaceEquiv Ω n ω.1 i := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

@[simp] lemma sampleSpaceEquiv_last (Ω : Type u) (n : ℕ) (ω : SampleSpace Ω (n + 1)) :
    sampleSpaceEquiv Ω (n + 1) ω (Fin.last n) = ω.2 := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Ω) (sampleSpaceEquiv Ω n ω.1) ω.2 (Fin.last n) = _
  exact Fin.snoc_last _ _

variable {Ω : Type u} [Fintype Ω]

end Riesz.Moments
end

section
/-! A finite, shifted Khintchine bound derived from genuine product moments. -/
namespace Oscillation
noncomputable section
open scoped BigOperators
open Riesz.Moments
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open scoped BigOperators
open Finset

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 300000

end
end Oscillation
end

section
/-! Average the child functions before comparing their maximum, as in r15. -/
namespace Oscillation
noncomputable section
open Finset

end
end Oscillation
end

section
/-! Summing the actual row gains gives the full oscillation drift. -/
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

end
end Oscillation
end

section
/-! The actual horizontal sampling process and its compensated exponential bound. -/
namespace Oscillation
noncomputable section
open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets
open scoped ENNReal

end
end Oscillation
end

section
namespace Oscillation
noncomputable section
open MeasureTheory Riesz.PointSets

abbrev coordinateSampleLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => μI)

abbrev pointSampleLaw (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin n => μI.prod μI)

def splitCoordinates (n : ℕ) : (Fin n → ℝ × ℝ) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)

lemma splitCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (splitCoordinates n) (pointSampleLaw n)
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) :=
  measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => μI) (fun _ => μI)

lemma pairCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (splitCoordinates n).symm
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) (pointSampleLaw n) :=
  MeasurePreserving.symm (splitCoordinates n) (splitCoordinates_measurePreserving n)

lemma pointSampleLaw_eq_unifPts (n : ℕ) : pointSampleLaw n = unifPts n := by
  unfold pointSampleLaw unifPts
  simp_rw [unitSq_eq]

lemma integrable_pairCoordinates_iff {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ) :
    Integrable (fun UV : (Fin n → ℝ) × (Fin n → ℝ) => F (fun i => (UV.1 i, UV.2 i)))
      ((coordinateSampleLaw n).prod (coordinateSampleLaw n)) ↔
      Integrable F (pointSampleLaw n) :=
  (pairCoordinates_measurePreserving n).integrable_comp_emb
    (splitCoordinates n).symm.measurableEmbedding

lemma integral_point_eq_product {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ) :
    (∫ P, F P ∂pointSampleLaw n) =
      ∫ UV : (Fin n → ℝ) × (Fin n → ℝ), F (fun i => (UV.1 i, UV.2 i))
        ∂((coordinateSampleLaw n).prod (coordinateSampleLaw n)) :=
  ((pairCoordinates_measurePreserving n).integral_comp' F).symm

lemma integral_point_eq_vertical_horizontal {n : ℕ} (F : (Fin n → ℝ × ℝ) → ℝ)
    (hF : Integrable F (pointSampleLaw n)) :
    (∫ P, F P ∂pointSampleLaw n) =
      ∫ V, ∫ U, F (fun i => (U i, V i)) ∂coordinateSampleLaw n ∂coordinateSampleLaw n := by
  rw [integral_point_eq_product]
  exact integral_prod_symm _ ((integrable_pairCoordinates_iff F).mpr hF)

lemma ae_pointSampleLaw_mem_Ioc (n : ℕ) :
    ∀ᵐ P ∂pointSampleLaw n, ∀ i, (P i).1 ∈ Set.Ioc (0 : ℝ) 1 ∧
      (P i).2 ∈ Set.Ioc (0 : ℝ) 1 := by
  have hI : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 := ae_iff.mpr μI_compl_Ioc
  have hprod : ∀ᵐ z ∂μI.prod μI, z.1 ∈ Set.Ioc (0 : ℝ) 1 ∧ z.2 ∈ Set.Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
    filter_upwards [hI] with u hu
    filter_upwards [hI] with v hv
    exact ⟨hu, hv⟩
  apply ae_all_iff.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI.prod μI) (i := i) hprod

end
end Oscillation
end

section

end

section
/-!
# The objects of Section 1 of the manuscript, in its own notation

Auditor's supplement (not part of the audited archive).

| Manuscript (Section 1) | Here |
| --- | --- |
| `F_χ(x,y) = Σ_i χ_i 1{P_i ∈ [0,x] × [0,y]}` | `R56Audit.F χ P x y` |
| `‖F_χ‖∞`, the supremum of `|F_χ|` over `[0,1]²` | `R56Audit.supNorm χ P` |

Colorings are `χ : Fin n → ℤˣ`, that is `χ ∈ {±1}ⁿ`; the points are `P : Fin n → ℝ × ℝ`.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

open Classical in
/-- The signed counting function `F_χ(x,y) = Σ_i χ_i 1[P_i ∈ [0,x] × [0,y]]`. -/
def F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) : ℝ :=
  ∑ i, if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0

/-- `‖F_χ‖∞ = sup_{(x,y) ∈ [0,1]²} |F_χ(x,y)|`, the largest imbalance on an anchored
rectangle. The family is bounded by `n` (`abs_F_le`), so this is a genuine supremum. -/
def supNorm (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ⨆ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, |F χ P z.1 z.2|

/-! ### Elementary facts -/

lemma abs_F_le (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) : |F χ P x y| ≤ n := by
  classical
  unfold F
  calc |∑ i, (if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0)|
      ≤ ∑ i, |(if P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) then (((χ i : ℤˣ) : ℤ) : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rcases Int.units_eq_one_or (χ i) with h | h <;> simp [h]
        · simp
    _ = n := by simp

lemma bddAbove_F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) :
    BddAbove (Set.range fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => |F χ P z.1 z.2|) :=
  ⟨n, by rintro _ ⟨z, rfl⟩; exact abs_F_le χ P _ _⟩

/-- Every anchored rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]` has imbalance at most
`‖F_χ‖∞`. -/
lemma le_supNorm (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |F χ P x y| ≤ supNorm χ P :=
  le_ciSup (f := fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 => |F χ P z.1 z.2|)
    (bddAbove_F χ P) (⟨x, hx⟩, ⟨y, hy⟩)

/-- `F_χ` written with the four coordinate inequalities. -/
lemma F_eq_filter (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) :
    F χ P x y = ∑ t ∈ Finset.univ.filter
      (fun t => 0 ≤ (P t).1 ∧ (P t).1 ≤ x ∧ 0 ≤ (P t).2 ∧ (P t).2 ≤ y),
        (((χ t : ℤˣ) : ℤ) : ℝ) := by
  classical
  unfold F
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : P t ∈ Set.Icc (0 : ℝ × ℝ) (x, y) ↔
      (0 ≤ (P t).1 ∧ (P t).1 ≤ x ∧ 0 ≤ (P t).2 ∧ (P t).2 ≤ y) := by
    simp only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero]
    tauto
  by_cases hq : P t ∈ Set.Icc (0 : ℝ × ℝ) (x, y)
  · rw [if_pos hq, if_pos (h.mp hq)]
  · rw [if_neg hq, if_neg (fun h' => hq (h.mpr h'))]

end

end R56Audit
end

section
/-!
# `‖F_χ‖∞` is a maximum over finitely many rectangles

An anchored rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]` contains the same sample points as
one whose sides are `0` or coordinates of sample points. Hence the supremum defining
`‖F_χ‖∞` is attained (`exists_eq_supNorm`): it is the largest imbalance of an anchored
rectangle `[0,x] × [0,y]` with `x, y ∈ [0,1]`. It is also a measurable function of the sample
(`measurable_supNorm`), so the events of Theorem 1.1 and of Proposition 2.7 are measurable
(`measurableSet_forall_le_supNorm`, `measurableSet_supNorm_le`, `measurableSet_exists_supNorm_le`)
and their probabilities are not merely outer measures.

`one_le_supNorm` is the lowest-point argument of the proof of Theorem 1.1: "The rectangle
`[0,1] × [0, min_i V_i]` \[…\] contains just the lowest point, which is unique since all
heights are distinct."

Auditor's supplement (not part of the audited archive).
-/

namespace R56Audit

open MeasureTheory

noncomputable section

variable {n : ℕ}

end

end R56Audit
end

section
/-!
# Oscillation, midpoint, and Lemma 2.1 of the manuscript (vertical comparison)

Auditor's supplement (not part of the audited archive).

Section 2.1 of the manuscript defines, for a function `f` of the height and a vertical
interval `B`,

`osc_B f = max_B f - min_B f`,   `mid_B f = (max_B f + min_B f) / 2`,

where the extrema are over `y ∈ B`. All functions considered there take finitely many values,
so the extrema exist. Here `max_B f` and `min_B f` are `sSup (f '' B)` and `sInf (f '' B)`;
`maxOn_mem` and `minOn_mem` show that for a function with finitely many values on a nonempty
`B` they are attained, i.e. they are the maximum and the minimum. `osc_const_mul` is the
manuscript's "Clearly `osc_B (c f) = |c| osc_B f` for real `c`"; with these definitions of
the extrema it holds for every `B` and every `f`. `osc_neg` is its case `c = -1`, the
manuscript's "`osc_B (-g) = osc_B g`".

`osc_add_le` is the triangle inequality `osc_B (f + g) ≤ osc_B f + osc_B g`. It is proved as
in the manuscript, "because the maximum of `f+g` on `B` is at most `max_B f + max_B g`, and
its minimum is at least `min_B f + min_B g`": these two facts are `maxOn_add_le` and
`add_minOn_le`. `osc_sum_le` is the triangle inequality for finite sums. (The reverse
triangle inequality is in `StepOsc.lean`.)

Section 2.2 cuts `J` into blocks (`block`, `iUnion_block`, `block_disjoint`) and sets
`R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`, the inner region. `iUnion_inner_blocks` shows that the
union `B_2 ∪ ⋯ ∪ B_{b-1}` of the inner blocks is the interval `[s + L, s + (b-1) L)`, and
`inner_blocks_nonempty` that this interval is not empty when `b ≥ 3`.

`vertical_comparison` is **Lemma 2.1** as stated: for `J` cut into `b` blocks
`B_1, …, B_b` of equal length, from bottom to top, and `f` with finitely many values on `J`,

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof is the one of the manuscript, sentence by sentence:

* `maxOn_sub_minOn_le_osc`, `maxOn_sub_minOn_eq`: the first display. Its first line is
  `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`,
  and its second line is the same with `B_1` and `B_b` exchanged. "Since `J` contains `B_1`
  and `B_b`", the inequality holds, and the equality holds because "the extrema of `f` on a
  block `B` are `mid_B f ± ½ osc_B f`" (`maxOn_eq_mid_add`, `minOn_eq_mid_sub`);
* `half_osc_add_abs_mid_sub_le`: "Taking the larger of the two right-hand sides,
  `osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`";
* `osc_mono`: "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`";
* `vertical_comparison_sets`: "Adding these `b-2` inequalities and twice the last display
  proves (4)."

It uses nothing about the blocks except that they are nonempty subsets of `J`
(`vertical_comparison_sets`). This file does not use the archive.
-/

namespace R56Audit

noncomputable section

variable {α : Type*}

/-- `max_B f`, as a supremum. -/
def maxOn (B : Set α) (f : α → ℝ) : ℝ := sSup (f '' B)

/-- `min_B f`, as an infimum. -/
def minOn (B : Set α) (f : α → ℝ) : ℝ := sInf (f '' B)

/-- The oscillation `osc_B f = max_B f - min_B f` of display (3). -/
def osc (B : Set α) (f : α → ℝ) : ℝ := maxOn B f - minOn B f

/-- The midpoint `mid_B f = (max_B f + min_B f) / 2` of display (3). -/
def mid (B : Set α) (f : α → ℝ) : ℝ := (maxOn B f + minOn B f) / 2

lemma le_maxOn {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    f y ≤ maxOn B f :=
  le_csSup hf.bddAbove (Set.mem_image_of_mem f hy)

lemma minOn_le {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    minOn B f ≤ f y :=
  csInf_le hf.bddBelow (Set.mem_image_of_mem f hy)

lemma maxOn_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, f y ≤ c) :
    maxOn B f ≤ c := by
  apply csSup_le (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

lemma le_minOn {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, c ≤ f y) :
    c ≤ minOn B f := by
  apply le_csInf (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/-- The extrema are `mid_B f ± osc_B f / 2`. -/
lemma maxOn_eq_mid_add (B : Set α) (f : α → ℝ) : maxOn B f = mid B f + osc B f / 2 := by
  unfold mid osc; ring

lemma minOn_eq_mid_sub (B : Set α) (f : α → ℝ) : minOn B f = mid B f - osc B f / 2 := by
  unfold mid osc; ring

lemma minOn_le_maxOn {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    minOn B f ≤ maxOn B f := by
  obtain ⟨y, hy⟩ := hB
  exact (minOn_le hf hy).trans (le_maxOn hf hy)

lemma osc_nonneg {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    0 ≤ osc B f :=
  sub_nonneg.mpr (minOn_le_maxOn hB hf)

/-- A difference of two values on `B` is at most the oscillation. -/
lemma sub_le_osc {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y y' : α} (hy : y ∈ B)
    (hy' : y' ∈ B) : f y - f y' ≤ osc B f := by
  have h1 := le_maxOn hf hy
  have h2 := minOn_le hf hy'
  unfold osc
  linarith

/-- The oscillation is the least bound for the differences of two values on `B`. -/
lemma osc_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ}
    (h : ∀ y ∈ B, ∀ y' ∈ B, f y - f y' ≤ c) : osc B f ≤ c := by
  have h1 : maxOn B f ≤ minOn B f + c := by
    apply maxOn_le hB
    intro y hy
    have : f y - c ≤ minOn B f := le_minOn hB (fun y' hy' => by linarith [h y hy y' hy'])
    linarith
  unfold osc
  linarith

/-- The extrema over a subset lie between the extrema over the set. -/
lemma maxOn_mono {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : maxOn A f ≤ maxOn B f :=
  maxOn_le hA fun _ hy => le_maxOn hf (hAB hy)

lemma minOn_anti {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : minOn B f ≤ minOn A f :=
  le_minOn hA fun _ hy => minOn_le hf (hAB hy)

lemma maxOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    maxOn B f = maxOn B g := by
  unfold maxOn
  rw [Set.image_congr h]

lemma minOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    minOn B f = minOn B g := by
  unfold minOn
  rw [Set.image_congr h]

lemma osc_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) : osc B f = osc B g := by
  unfold osc
  rw [maxOn_congr h, minOn_congr h]

lemma mid_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) : mid B f = mid B g := by
  unfold mid
  rw [maxOn_congr h, minOn_congr h]

/-- "Clearly `osc_B (c f) = |c| osc_B f` for real `c`." With the extrema defined as `sSup` and
`sInf`, this needs no hypothesis on `B` or on `f`. -/
theorem osc_const_mul (B : Set α) (f : α → ℝ) (c : ℝ) :
    osc B (fun y => c * f y) = |c| * osc B f := by
  unfold osc maxOn minOn
  simp only [sSup_image', sInf_image']
  rcases le_total 0 c with hc | hc
  · -- `c ≥ 0`: the maximum and the minimum are multiplied by `c`
    rw [← Real.mul_iSup_of_nonneg hc, ← Real.mul_iInf_of_nonneg hc, abs_of_nonneg hc]
    ring
  · -- `c ≤ 0`: the maximum of `c f` is `c` times the minimum of `f`, and conversely
    rw [← Real.mul_iInf_of_nonpos hc, ← Real.mul_iSup_of_nonpos hc, abs_of_nonpos hc]
    ring

/-- Adding a constant adds it to the maximum. -/
lemma maxOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : maxOn B (fun y => f y + c) = maxOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · exact maxOn_le hB fun y hy => by linarith [le_maxOn hf hy]
  · have : maxOn B f ≤ maxOn B (fun y => f y + c) - c :=
      maxOn_le hB fun y hy => by linarith [le_maxOn hfc hy]
    linarith

/-- Adding a constant adds it to the minimum. -/
lemma minOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : minOn B (fun y => f y + c) = minOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · have : minOn B (fun y => f y + c) - c ≤ minOn B f :=
      le_minOn hB fun y hy => by linarith [minOn_le hfc hy]
    linarith
  · exact le_minOn hB fun y hy => by linarith [minOn_le hf hy]

/-- **Shift invariance**: adding a constant does not change the oscillation. -/
lemma osc_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : osc B (fun y => f y + c) = osc B f := by
  unfold osc
  rw [maxOn_add_const hB hf, minOn_add_const hB hf]
  ring

/-- Adding a constant `c` adds `c` to the midpoint. -/
lemma mid_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : mid B (fun y => f y + c) = mid B f + c := by
  unfold mid
  rw [maxOn_add_const hB hf, minOn_add_const hB hf]
  ring

/-- "the maximum of `f+g` on `B` is at most `max_B f + max_B g`": the first half of the
manuscript's reason for the triangle inequality. -/
lemma maxOn_add_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : maxOn B (fun y => f y + g y) ≤ maxOn B f + maxOn B g :=
  -- every value of `f + g` on `B` is at most `max_B f + max_B g`
  maxOn_le hB fun _ hy => add_le_add (le_maxOn hf hy) (le_maxOn hg hy)

/-- "its minimum is at least `min_B f + min_B g`": the second half of the manuscript's reason
for the triangle inequality; "its" refers to `f+g` on `B`. -/
lemma add_minOn_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : minOn B f + minOn B g ≤ minOn B (fun y => f y + g y) :=
  -- every value of `f + g` on `B` is at least `min_B f + min_B g`
  le_minOn hB fun _ hy => add_le_add (minOn_le hf hy) (minOn_le hg hy)

/-- **The triangle inequality** `osc_B (f + g) ≤ osc_B f + osc_B g`, "because the maximum of
`f+g` on `B` is at most `max_B f + max_B g`, and its minimum is at least `min_B f + min_B g`"
(`maxOn_add_le`, `add_minOn_le`). -/
lemma osc_add_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : osc B (fun y => f y + g y) ≤ osc B f + osc B g := by
  -- the maximum of `f + g`, and its minimum
  have h1 := maxOn_add_le hB hf hg
  have h2 := add_minOn_le hB hf hg
  -- the oscillation is the maximum minus the minimum
  unfold osc
  linarith

/-- "`osc_B (-g) = osc_B g`": the case `c = -1` of `osc_B (c f) = |c| osc_B f`. -/
lemma osc_neg (B : Set α) (g : α → ℝ) : osc B (fun y => -g y) = osc B g := by
  have h : (fun y => -g y) = fun y => -1 * g y := funext fun y => (neg_one_mul (g y)).symm
  rw [h, osc_const_mul, abs_neg, abs_one, one_mul]

/-- The triangle inequality for finite sums. -/
lemma osc_sum_le {ι : Type*} (s : Finset ι) {B : Set α} {f : ι → α → ℝ} (hB : B.Nonempty)
    (hf : ∀ k ∈ s, ((f k) '' B).Finite) :
    osc B (fun y => ∑ k ∈ s, f k y) ≤ ∑ k ∈ s, osc B (f k) :=
  osc_le hB fun y hy y' hy' => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k hk => sub_le_osc (hf k hk) hy hy'

/-- "By the triangle inequality for the oscillation,
`Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`": `b` times the oscillation of the average of
`b` functions is at most the sum of their oscillations. -/
lemma card_mul_osc_avg_le {ι : Type*} [Fintype ι] [Nonempty ι] {B : Set α} {f : ι → α → ℝ}
    (hB : B.Nonempty) (hf : ∀ k, ((f k) '' B).Finite) :
    (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι) ≤
      ∑ k, osc B (f k) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `Σ_k f_k` is `b` times the average, and `osc_B (b f) = b osc_B f`
  have hsum : (fun y => ∑ k, f k y) =
      fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι) := by
    funext y
    field_simp
  calc (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι)
      = osc B (fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι)) := by
        rw [osc_const_mul, abs_of_pos hc]
    _ = osc B (fun y => ∑ k, f k y) := by rw [← hsum]
    _ ≤ ∑ k, osc B (f k) := osc_sum_le Finset.univ hB fun k _ => hf k

/-! ### Blocks -/

/-- The block `B_{ℓ+1} = [s + ℓ L, s + (ℓ+1) L)` of the vertical interval
`J = [s, s + b L)`: closed at the bottom, open at the top. Blocks are numbered from `0` here
and from `1` in the manuscript. -/
def block (s L : ℝ) (ℓ : ℕ) : Set ℝ := Set.Ico (s + ℓ * L) (s + (ℓ + 1) * L)

lemma block_nonempty (s : ℝ) {L : ℝ} (hL : 0 < L) (ℓ : ℕ) : (block s L ℓ).Nonempty :=
  ⟨s + ℓ * L, ⟨le_rfl, by nlinarith⟩⟩

lemma block_subset (s : ℝ) {L : ℝ} (hL : 0 < L) {b ℓ : ℕ} (hℓ : ℓ < b) :
    block s L ℓ ⊆ Set.Ico s (s + b * L) := by
  rintro y ⟨h1, h2⟩
  have h0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hb : (ℓ : ℝ) + 1 ≤ b := by exact_mod_cast hℓ
  constructor
  · nlinarith
  · nlinarith

/-! ### Lemma 2.1 -/

/-- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`": the oscillation
on a nonempty subset `A` of `J` is at most the oscillation on `J`. -/
lemma osc_mono {A J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAJ : A ⊆ J)
    (hf : (f '' J).Finite) : osc A f ≤ osc J f := by
  -- the extrema of `f` on `A` lie between its extrema on `J`
  have h1 := maxOn_mono hA hAJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The inequality in the first display of the proof of Lemma 2.1, for two nonempty subsets
`A` (the bottom block `B_1`) and `C` (the top block `B_b`) of `J`: "Since `J` contains `B_1`
and `B_b`, \[…\] `osc_J f ≥ max_{B_b} f - min_{B_1} f`". With `A` and `C` exchanged, it is the
inequality "`osc_J f ≥ max_{B_1} f - min_{B_b} f`" of the second line. -/
lemma maxOn_sub_minOn_le_osc {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hC : C.Nonempty)
    (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) : maxOn C f - minOn A f ≤ osc J f := by
  -- the maximum on `C` is at most the maximum on `J`, and the minimum on `A` is at least the
  -- minimum on `J`
  have h1 := maxOn_mono hC hCJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The equality in the first display of the proof of Lemma 2.1, for two sets `A` (the bottom
block `B_1`) and `C` (the top block `B_b`): since "the extrema of `f` on a block `B` are
`mid_B f ± ½ osc_B f`",
"`max_{B_b} f - min_{B_1} f = (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`".
With `A` and `C` exchanged, it is the equality of the second line of that display: its
right-hand side `(osc_{B_b} f + osc_{B_1} f)/2 + (mid_{B_1} f - mid_{B_b} f)` is the
manuscript's `(osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`. -/
lemma maxOn_sub_minOn_eq (A C : Set α) (f : α → ℝ) :
    maxOn C f - minOn A f = (osc A f + osc C f) / 2 + (mid C f - mid A f) := by
  -- `max_C f = mid_C f + ½ osc_C f` and `min_A f = mid_A f - ½ osc_A f`
  rw [maxOn_eq_mid_add C f, minOn_eq_mid_sub A f]
  ring

/-- The first part of the proof of Lemma 2.1, for two nonempty subsets `A` (the bottom block
`B_1`) and `C` (the top block `B_b`) of `J`:
"`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`". -/
theorem half_osc_add_abs_mid_sub_le {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty)
    (hC : C.Nonempty) (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) :
    (osc A f + osc C f) / 2 + |mid C f - mid A f| ≤ osc J f := by
  -- the first line of the first display, `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`
  have h1 : (osc A f + osc C f) / 2 + (mid C f - mid A f) ≤ osc J f :=
    (maxOn_sub_minOn_eq A C f).symm.trans_le (maxOn_sub_minOn_le_osc hA hC hAJ hCJ hf)
  -- the second line, `osc_J f ≥ max_{B_1} f - min_{B_b} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`: the two blocks exchanged
  have h2 : (osc A f + osc C f) / 2 - (mid C f - mid A f) ≤ osc J f := by
    have h := (maxOn_sub_minOn_eq C A f).symm.trans_le
      (maxOn_sub_minOn_le_osc hC hA hCJ hAJ hf)
    linarith
  -- "Taking the larger of the two right-hand sides"
  rcases le_total 0 (mid C f - mid A f) with H | H
  · rw [abs_of_nonneg H]
    exact h1
  · rw [abs_of_nonpos H]
    linarith

/-- **Lemma 2.1** for arbitrary nonempty subsets `B_1, …, B_b` of a set `J` in place of the
blocks of an interval: if `f` has finitely many values on `J`, then

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof of the manuscript uses nothing else about the blocks. -/
theorem vertical_comparison_sets {b : ℕ} (hb : 2 ≤ b) (J : Set α) (B : Fin b → Set α)
    (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (f : α → ℝ) (hf : (f '' J).Finite) :
    ∑ ℓ : Fin b, osc (B ℓ) f +
        2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f := by
  classical
  -- the bottom block and the top block are different blocks
  have hfirst : (⟨0, by omega⟩ : Fin b) ≠ ⟨b - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  -- "`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`"
  have h2 := half_osc_add_abs_mid_sub_le (hne (⟨0, by omega⟩ : Fin b))
    (hne (⟨b - 1, by omega⟩ : Fin b)) (hsub _) (hsub _) hf
  -- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`."
  have h1 : ∀ ℓ, osc (B ℓ) f ≤ osc J f := fun ℓ => osc_mono (hne ℓ) (hsub ℓ) hf
  have hrest : ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩,
      osc (B ℓ) f ≤ ((b : ℝ) - 2) * osc J f := by
    calc ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc (B ℓ) f
        ≤ ∑ _ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc J f :=
          Finset.sum_le_sum fun ℓ _ => h1 ℓ
      _ = ((b : ℝ) - 2) * osc J f := by
          rw [Finset.sum_const, Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : ((b - 1 - 1 : ℕ) : ℝ) = (b : ℝ) - 2 := by
            rw [Nat.sub_sub, Nat.cast_sub hb]
            norm_num
          rw [this]
  -- "Adding these `b-2` inequalities and twice the last display proves (4)."
  have e1 := Finset.add_sum_erase Finset.univ (fun ℓ : Fin b => osc (B ℓ) f)
    (Finset.mem_univ (⟨0, by omega⟩ : Fin b))
  have e2 := Finset.add_sum_erase (Finset.univ.erase (⟨0, by omega⟩ : Fin b))
    (fun ℓ : Fin b => osc (B ℓ) f) (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩)
  linarith

/-- **Lemma 2.1 (vertical comparison)**, display (4). Partition `J = [s, s + b L)` into
blocks `B_1, …, B_b` of equal length `L`, from bottom to top, and let `f` be a function on
`J` with finitely many values. Then

`b · osc_J f ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

Only `b ≥ 2` is used (the manuscript has `b ≥ 3` throughout). -/
theorem vertical_comparison {b : ℕ} (hb : 2 ≤ b) (s : ℝ) {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (hf : (f '' Set.Ico s (s + b * L)).Finite) :
    ∑ ℓ : Fin b, osc (block s L ℓ) f +
        2 * |mid (block s L (b - 1)) f - mid (block s L 0) f| ≤
      b * osc (Set.Ico s (s + b * L)) f :=
  vertical_comparison_sets hb (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt) f hf

end

end R56Audit
end

section
/-!
# Fact 2.2 of the manuscript (sums of symmetric variables), for real random variables

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables. Suppose that
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` for every `i`, where `σ > 0`. Then
`E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

Symmetric variables are "variables that have the same distribution as their negatives": the
hypothesis on `X_i` is `IdentDistrib (X i) (fun ω => -X i ω) μ μ`. The proof is the one of
Appendix A.1: the shift does not hurt; two moments; from moments to the absolute value
(Hölder with exponents `3/2` and `3`).

`fact_2_2_general` is the statement for random variables on an arbitrary probability space.
(`fact_2_2_uniform` in `UniformDigits.lean` is the special case of functions of independent
uniform digits, which is the form in which Lemma 2.3 uses the fact.) This file uses Mathlib
only, not the archive.

The three steps of Appendix A.1, with `X = Σ_i X_i`:

* the shift does not hurt: `identDistrib_sum_neg` (`X` and `-X` have the same distribution),
  `integral_abs_add_eq_integral_abs_sub` (`E|θ + X| = E|θ - X|`) and
  `integral_abs_le_integral_abs_add_of_symm` (`E|θ + X| ≥ E|X|`);
* two moments: `integral_pow_eq_zero_of_symm` (`E X_i = 0`, and also `E X_i³ = 0`),
  `sum_moments` (`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`) and `sum_fourth_moment_le`
  (`E X⁴ ≤ 3m²σ⁴`). The proof of `sum_moments` is by induction on the number of variables
  (one variable is added at a time, with `moments_add_of_indepFun`), not by expanding `X⁴`
  and counting the surviving terms as the manuscript does. The manuscript's term
  `6 Σ_{i<j} E X_i² E X_j²` appears in the evaluated form `3m(m-1)σ⁴`, which is the same
  number because every `E X_i² = σ²` and there are `m(m-1)/2` pairs `i < j`;
* from moments to the absolute value: `integral_sq_le_rpow_mul_rpow` (Hölder's inequality,
  `E X² ≤ (E|X|)^{2/3} (E X⁴)^{1/3}`), `integral_sq_pow_three_le` (its cube,
  `(E X²)³ ≤ (E|X|)² E X⁴`) and `mul_sqrt_le_of_moments` (the arithmetic).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory

noncomputable section

section General

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The shift does not hurt -/

/-- Independent symmetric variables are jointly symmetric: the families `(X_i)` and `(-X_i)`
have the same joint law, namely the product of the common marginal laws. -/
lemma identDistrib_neg_of_iIndepFun {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => -X i ω) μ μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  have hnX : ∀ i, AEMeasurable (fun ω => -X i ω) μ := fun i => (hsymm i).aemeasurable_snd
  have hneg : iIndepFun (fun i ω => -X i ω) μ :=
    hindep.comp (fun _ x => -x) fun _ => measurable_neg
  refine ⟨aemeasurable_pi_iff.mpr hX, aemeasurable_pi_iff.mpr hnX, ?_⟩
  rw [hindep.map_fun_eq_pi_map hX, hneg.map_fun_eq_pi_map hnX]
  congr 1
  funext i
  exact (hsymm i).map_eq

/-- A finite sum `X` of independent symmetric variables is symmetric: `X` and `-X` have the
same distribution. -/
lemma identDistrib_sum_neg {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) :
    IdentDistrib (fun ω => ∑ i, X i ω) (fun ω => -∑ i, X i ω) μ μ := by
  have hsum : Measurable fun v : ι → ℝ => ∑ i, v i :=
    Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i
  have h := (identDistrib_neg_of_iIndepFun X hindep hsymm).comp hsum
  simpa only [Function.comp_def, Finset.sum_neg_distrib] using h

/-- **The shift does not hurt**, the equality (Appendix A.1): "So `X` and `-X` have the same
distribution, and `E|θ + X| = E|θ - X|`." The lemma is the second half of this sentence, for
a real random variable `X` that has the same distribution as `-X`. (The first half, for
`X = Σ_i X_i`, is `identDistrib_sum_neg`.) No integrability hypothesis is needed, because
identically distributed functions have the same integral (`IdentDistrib.integral_eq`). -/
lemma integral_abs_add_eq_integral_abs_sub {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (θ : ℝ) :
    ∫ ω, |θ + X ω| ∂μ = ∫ ω, |θ - X ω| ∂μ := by
  -- apply the measurable function `x ↦ |θ + x|` to `X` and to `-X`
  have hg : Measurable fun x : ℝ => |θ + x| :=
    (continuous_const.add continuous_id).abs.measurable
  have h := (hsymm.comp hg).integral_eq
  simpa only [Function.comp_def, sub_eq_add_neg] using h

/-- **The shift does not hurt** (Appendix A.1): `E|θ + X| ≥ E|X|` for a symmetric integrable
variable `X`. "Averaging the two and using `|θ + x| + |θ - x| ≥ 2|x|` gives
`E|θ + X| ≥ E|X|`." The two are `E|θ + X|` and `E|θ - X|`, which are equal by
`integral_abs_add_eq_integral_abs_sub`. -/
lemma integral_abs_le_integral_abs_add_of_symm [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsymm : IdentDistrib X (fun ω => -X ω) μ μ) (hX : Integrable X μ) (θ : ℝ) :
    ∫ ω, |X ω| ∂μ ≤ ∫ ω, |θ + X ω| ∂μ := by
  have hp : Integrable (fun ω => |θ + X ω|) μ := ((integrable_const θ).add hX).abs
  have hm : Integrable (fun ω => |θ - X ω|) μ := ((integrable_const θ).sub hX).abs
  -- `|θ + x| + |θ - x| ≥ 2|x|`, by the triangle inequality
  have hpoint : ∀ ω, |X ω| ≤ (|θ + X ω| + |θ - X ω|) / 2 := by
    intro ω
    have h := abs_sub (θ + X ω) (θ - X ω)
    have e : θ + X ω - (θ - X ω) = 2 * X ω := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  -- average `E|θ + X|` and `E|θ - X|`, which are equal
  calc ∫ ω, |X ω| ∂μ ≤ ∫ ω, (|θ + X ω| + |θ - X ω|) / 2 ∂μ :=
        integral_mono hX.abs ((hp.add hm).div_const 2) hpoint
    _ = (∫ ω, |θ + X ω| ∂μ + ∫ ω, |θ - X ω| ∂μ) / 2 := by
        rw [integral_div, integral_add hp hm]
    _ = ∫ ω, |θ + X ω| ∂μ := by
        rw [← integral_abs_add_eq_integral_abs_sub hsymm θ]
        ring

/-! ### Two moments -/

/-- A symmetric real random variable has vanishing odd moments: `E Y^k = 0` for odd `k`.

The case `k = 1` is the mean, because `Y ω ^ 1` is `Y ω` (`pow_one`). So this lemma covers
the manuscript's "Every `X_i` is symmetric and has a finite second moment, so `E X_i = 0`",
and there is no separate lemma for the mean; `sum_moments` uses the cases `k = 1` and
`k = 3`. No moment hypothesis is needed: if `Y ^ k` is not integrable, then its integral is
`0` by Mathlib's convention. -/
lemma integral_pow_eq_zero_of_symm {Y : Ω → ℝ} (h : IdentDistrib Y (fun ω => -Y ω) μ μ) {k : ℕ}
    (hk : Odd k) : ∫ ω, Y ω ^ k ∂μ = 0 := by
  have h1 := (h.comp (measurable_id.pow_const k)).integral_eq
  simp only [Function.comp_apply, id_eq, hk.neg_pow, integral_neg] at h1
  linarith

/-- On a finite measure space, a real function with an integrable fourth power has integrable
lower powers. -/
lemma integrable_pow_of_integrable_pow_four [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (h4 : Integrable (fun ω => Y ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Y ω ^ k) μ := by
  have h4' : Integrable (fun ω => ‖Y ω‖ ^ 4) μ := by
    simpa only [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using h4
  have hk' := integrable_norm_pow_of_le hY.aestronglyMeasurable hk h4'
  refine (integrable_norm_iff (hY.pow_const k).aestronglyMeasurable).mp ?_
  simpa only [norm_pow] using hk'

/-- **Two moments, one step.** Let `Y` and `T` be independent with finite fourth moments, and
let `E Y = E Y³ = 0`. Then `(Y + T)⁴` is integrable, `E (Y + T)² = E Y² + E T²` and
`E (Y + T)⁴ = E Y⁴ + 6 E Y² E T² + E T⁴`. -/
lemma moments_add_of_indepFun [IsFiniteMeasure μ] {Y T : Ω → ℝ} (hYT : IndepFun Y T μ)
    (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ)
    (hY4 : Integrable (fun ω => Y ω ^ 4) μ) (hT4 : Integrable (fun ω => T ω ^ 4) μ)
    (hY1 : ∫ ω, Y ω ∂μ = 0) (hY3 : ∫ ω, Y ω ^ 3 ∂μ = 0) :
    Integrable (fun ω => (Y ω + T ω) ^ 4) μ ∧
      ∫ ω, (Y ω + T ω) ^ 2 ∂μ = ∫ ω, Y ω ^ 2 ∂μ + ∫ ω, T ω ^ 2 ∂μ ∧
      ∫ ω, (Y ω + T ω) ^ 4 ∂μ =
        ∫ ω, Y ω ^ 4 ∂μ + 6 * ((∫ ω, Y ω ^ 2 ∂μ) * ∫ ω, T ω ^ 2 ∂μ) + ∫ ω, T ω ^ 4 ∂μ := by
  -- the mixed moments `E(Y^a T^b)` are finite and factor
  have hint : ∀ a b : ℕ, a ≤ 4 → b ≤ 4 → Integrable (fun ω => Y ω ^ a * T ω ^ b) μ :=
    fun a b ha hb =>
      (hYT.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integrable_mul
        (integrable_pow_of_integrable_pow_four hY hY4 ha)
        (integrable_pow_of_integrable_pow_four hT hT4 hb)
  have hfac : ∀ a b : ℕ, ∫ ω, Y ω ^ a * T ω ^ b ∂μ = (∫ ω, Y ω ^ a ∂μ) * ∫ ω, T ω ^ b ∂μ :=
    fun a b => hYT.integral_fun_comp_mul_comp hY hT
      (measurable_id.pow_const a).aestronglyMeasurable
      (measurable_id.pow_const b).aestronglyMeasurable
  have hY1' : ∫ ω, Y ω ^ 1 ∂μ = 0 := by simpa only [pow_one] using hY1
  have hY2 := integrable_pow_of_integrable_pow_four hY hY4 (k := 2) (by norm_num)
  have hT2 := integrable_pow_of_integrable_pow_four hT hT4 (k := 2) (by norm_num)
  have i11 := (hint 1 1 (by norm_num) (by norm_num)).const_mul 2
  have i31 := (hint 3 1 (by norm_num) (by norm_num)).const_mul 4
  have i22 := (hint 2 2 (by norm_num) (by norm_num)).const_mul 6
  have i13 := (hint 1 3 (by norm_num) (by norm_num)).const_mul 4
  -- the binomial expansions, with every mixed term in the form `Y ^ a * T ^ b`
  have e2 : (fun ω => (Y ω + T ω) ^ 2) =
      fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1) + T ω ^ 2 := by
    funext ω
    ring
  have e4 : (fun ω => (Y ω + T ω) ^ 4) = fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3) + T ω ^ 4 := by
    funext ω
    ring
  have s1 : Integrable (fun ω => Y ω ^ 2 + 2 * (Y ω ^ 1 * T ω ^ 1)) μ := hY2.add i11
  have t1 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1)) μ := hY4.add i31
  have t2 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2)) μ := t1.add i22
  have t3 : Integrable (fun ω => Y ω ^ 4 + 4 * (Y ω ^ 3 * T ω ^ 1) +
      6 * (Y ω ^ 2 * T ω ^ 2) + 4 * (Y ω ^ 1 * T ω ^ 3)) μ := t2.add i13
  refine ⟨?_, ?_, ?_⟩
  · rw [e4]
    exact t3.add hT4
  · rw [e2, integral_add s1 hT2, integral_add hY2 i11, integral_const_mul, hfac, hY1']
    ring
  · rw [e4, integral_add t3 hT4, integral_add t2 i13, integral_add t1 i22, integral_add hY4 i31,
      integral_const_mul, integral_const_mul, integral_const_mul, hfac 3 1, hfac 2 2, hfac 1 3,
      hY1', hY3]
    ring

/-- **Two moments** (Appendix A.1). For independent symmetric variables with `E X_i² = σ²` and
finite fourth moments, the sum `X` over a set of `m` indices has a finite fourth moment,
`E X² = mσ²` and `E X⁴ = Σ_i E X_i⁴ + 3m(m-1)σ⁴`.

The proof is by induction on the number of variables (one variable is added at a time, with
`moments_add_of_indepFun`), not by expanding `X⁴` and counting the surviving terms as the
manuscript does. The manuscript's term `6 Σ_{i<j} E X_i² E X_j²` appears here in the
evaluated form `3m(m-1)σ⁴`, which is the same number because every `E X_i² = σ²` and there
are `m(m-1)/2` pairs `i < j`. -/
lemma sum_moments [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (s : Finset ι) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 4) μ ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = s.card * σ ^ 2 ∧
      ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ =
        ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ + 3 * s.card * (s.card - 1) * σ ^ 4 := by
  classical
  have hX : ∀ i, AEMeasurable (X i) μ := fun i => (hsymm i).aemeasurable_fst
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨ihi, ih2, ih4⟩ := ih
    have hT : AEMeasurable (fun ω => ∑ j ∈ s, X j ω) μ :=
      Finset.aemeasurable_fun_sum s fun j _ => hX j
    -- the new variable is independent of the partial sum
    have hYT : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hindep.indepFun_finsetSum_of_notMem₀ hX hi).symm
      have e : (∑ j ∈ s, X j) = fun ω => ∑ j ∈ s, X j ω := by
        funext ω
        simp
      rwa [e] at h
    -- its odd moments vanish by symmetry
    obtain ⟨hi4, hm2, hm4⟩ := moments_add_of_indepFun hYT (hX i) hT (h4i i) ihi
      (by simpa using integral_pow_eq_zero_of_symm (hsymm i) (k := 1) (by decide))
      (integral_pow_eq_zero_of_symm (hsymm i) (by decide))
    simp only [Finset.sum_insert hi]
    refine ⟨hi4, ?_, ?_⟩
    · rw [hm2, h2 i, ih2, Finset.card_insert_of_notMem hi]
      push_cast
      ring
    · rw [hm4, h2 i, ih2, ih4, Finset.card_insert_of_notMem hi]
      push_cast
      ring

/-- **Two moments** (Appendix A.1), the bound on the fourth moment: if moreover
`E X_i⁴ ≤ 3σ⁴`, then `E X⁴ ≤ 3mσ⁴ + 3m(m-1)σ⁴ = 3m²σ⁴`. -/
lemma sum_fourth_moment_le [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ) (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ) {σ : ℝ}
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2) (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4) (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ ≤ 3 * (s.card * σ ^ 2) ^ 2 := by
  have hsum : ∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ ≤ s.card * (3 * σ ^ 4) := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul s _ _ fun i _ => h4 i
  rw [(sum_moments X hindep hsymm h2 h4i s).2.2]
  linarith

/-! ### From moments to the absolute value -/

/-- **Hölder's inequality with exponents `3/2` and `3`** (Appendix A.1), applied to the factors
`|Y|^{2/3}` and `|Y|^{4/3}`: `E Y² ≤ (E|Y|)^{2/3} (E Y⁴)^{1/3}`. -/
lemma integral_sq_le_rpow_mul_rpow [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    ∫ ω, Y ω ^ 2 ∂μ ≤ (∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ) := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by norm_num [Real.holderConjugate_iff]
  have habs : AEMeasurable (fun ω => |Y ω|) μ := continuous_abs.measurable.comp_aemeasurable hY
  have h1 : Integrable (fun ω => |Y ω|) μ := by
    simpa only [pow_one] using
      (integrable_pow_of_integrable_pow_four hY h4 (k := 1) (by norm_num)).abs
  -- the two factors are nonnegative, their product is `Y²`
  have hf0 : ∀ ω, 0 ≤ |Y ω| ^ (2 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hg0 : ∀ ω, 0 ≤ |Y ω| ^ (4 / 3 : ℝ) := fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hfg : ∀ ω, |Y ω| ^ (2 / 3 : ℝ) * |Y ω| ^ (4 / 3 : ℝ) = Y ω ^ 2 := fun ω => by
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by norm_num), ← sq_abs,
      ← Real.rpow_natCast]
    norm_num
  -- the first factor to the power `3/2` is `|Y|`, the second to the power `3` is `Y⁴`
  have hfp : ∀ ω, (|Y ω| ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = |Y ω| := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hgq : ∀ ω, (|Y ω| ^ (4 / 3 : ℝ)) ^ (3 : ℝ) = Y ω ^ 4 := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _), ← (by decide : Even 4).pow_abs, ← Real.rpow_natCast]
    norm_num
  have hfm : MemLp (fun ω => |Y ω| ^ (2 / 3 : ℝ)) (ENNReal.ofReal (3 / 2)) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hf0 _), hfp] using h1
  have hgm : MemLp (fun ω => |Y ω| ^ (4 / 3 : ℝ)) (ENNReal.ofReal 3) μ := by
    rw [← integrable_norm_rpow_iff (habs.pow_const _).aestronglyMeasurable (by norm_num)
      (by simp), ENNReal.toReal_ofReal (by norm_num)]
    simpa only [Real.norm_of_nonneg (hg0 _), hgq] using h4
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) hfm hgm
  simp only [hfg, hfp, hgq] at h
  rwa [show (1 / (3 / 2) : ℝ) = 2 / 3 by norm_num] at h

/-- **From moments to the absolute value** (Appendix A.1): the cube of Hölder's inequality,
`(E Y²)³ ≤ (E|Y|)² E Y⁴`, in other words `E|Y| ≥ (E Y²)^{3/2} / (E Y⁴)^{1/2}`. -/
lemma integral_sq_pow_three_le [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ)
    (h4 : Integrable (fun ω => Y ω ^ 4) μ) :
    (∫ ω, Y ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
  have hA : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have hQ : 0 ≤ ∫ ω, Y ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  have hV : 0 ≤ ∫ ω, Y ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  calc (∫ ω, Y ω ^ 2 ∂μ) ^ 3
      ≤ ((∫ ω, |Y ω| ∂μ) ^ (2 / 3 : ℝ) * (∫ ω, Y ω ^ 4 ∂μ) ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hV (integral_sq_le_rpow_mul_rpow hY h4) 3
    _ = (∫ ω, |Y ω| ∂μ) ^ 2 * ∫ ω, Y ω ^ 4 ∂μ := by
        rw [mul_pow, ← Real.rpow_natCast (_ ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hA,
          ← Real.rpow_natCast (_ ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hQ]
        norm_num

end General

/-- The arithmetic at the end of Appendix A.1, with `A = E|X|` and `Q = E X⁴`: if
`(mσ²)³ ≤ A² Q` and `Q ≤ 3(mσ²)²`, then `A ≥ σ √(m/3)`. -/
lemma mul_sqrt_le_of_moments {m σ A Q : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ) (hA : 0 ≤ A)
    (h2 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * Q) (h4 : Q ≤ 3 * (m * σ ^ 2) ^ 2) :
    σ * Real.sqrt (m / 3) ≤ A := by
  have hkey : σ ^ 2 * (m / 3) ≤ A ^ 2 := by
    -- the claim is trivial for `m = 0`; for `m > 0` divide by `3m²σ⁴ > 0`
    rcases hm.eq_or_lt with rfl | hpos
    · rw [zero_div, mul_zero]
      exact sq_nonneg A
    · have hc : 0 < 3 * (m ^ 2 * σ ^ 4) := by positivity
      have h1 : (m * σ ^ 2) ^ 3 ≤ A ^ 2 * (3 * (m * σ ^ 2) ^ 2) :=
        h2.trans (mul_le_mul_of_nonneg_left h4 (sq_nonneg A))
      refine le_of_mul_le_mul_left ?_ hc
      linarith
  calc σ * Real.sqrt (m / 3) = Real.sqrt (σ ^ 2 * (m / 3)) := by
        rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
    _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hkey
    _ = A := Real.sqrt_sq hA

/-! ### Fact 2.2 -/

/-- **Fact 2.2 (sums of symmetric variables).** Let `X_i`, `i ∈ ι` (a finite index set with
`m` elements), be independent symmetric real random variables on a probability space, with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴` (in particular the fourth moments are finite), where
`σ > 0`. Then `E|θ + Σ_i X_i| ≥ σ √(m/3)` for every real `θ`. -/
theorem fact_2_2_general {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ)
    (hindep : iIndepFun X μ)
    (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = σ ^ 2)
    (h4i : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (h4 : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ 3 * σ ^ 4)
    (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ := by
  have hS : AEMeasurable (fun ω => ∑ i, X i ω) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hsymm i).aemeasurable_fst
  -- two moments: `X = Σ_i X_i` has `E X² = mσ²` and `E X⁴ ≤ 3m²σ⁴`; in particular `E|X| < ∞`
  obtain ⟨hS4, hm2, -⟩ := sum_moments X hindep hsymm h2 h4i Finset.univ
  have hm4 := sum_fourth_moment_le X hindep hsymm h2 h4i h4 Finset.univ
  rw [Finset.card_univ] at hm2 hm4
  have hS1 : Integrable (fun ω => ∑ i, X i ω) μ := by
    simpa only [pow_one] using
      integrable_pow_of_integrable_pow_four hS hS4 (k := 1) (by norm_num)
  -- the shift does not hurt: `E|θ + X| ≥ E|X|`
  have hshift : ∫ ω, |∑ i, X i ω| ∂μ ≤ ∫ ω, |θ + ∑ i, X i ω| ∂μ :=
    integral_abs_le_integral_abs_add_of_symm (identDistrib_sum_neg X hindep hsymm) hS1 θ
  -- from moments to the absolute value: `(E X²)³ ≤ (E|X|)² E X⁴`, so `E|X| ≥ σ √(m/3)`
  have hH := integral_sq_pow_three_le hS hS4
  rw [hm2] at hH
  exact (mul_sqrt_le_of_moments (Nat.cast_nonneg _) hσ (integral_nonneg fun ω => abs_nonneg _)
    hH hm4).trans hshift

end

end R56Audit
end

section
/-!
# Fact 2.2 for functions of independent uniform digits

Auditor's supplement (not part of the audited archive).

In the local experiment of Section 2.3 the randomness consists of independent uniform digits.
`fact_2_2_uniform` is Fact 2.2 (`fact_2_2_general`) in this setting: the probability space is
`ι → D` with the law `digitLaw ι D` of independent uniform digits, where `D` carries the
discrete σ-algebra. Its expectation is the finite average `Oscillation.finAvg`
(`integral_digitLaw`), the digits are independent (`ProbabilityTheory.iIndepFun_pi`), and a
function of one digit that is negated by a permutation of the digits is symmetric
(`identDistrib_coord_neg`).
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Oscillation

noncomputable section

/-! ### Independent uniform digits -/

section Uniform

variable {ι D : Type*} [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D]

/-- The law of independent uniform digits: the product over `ι` of the uniform law on `D`. -/
abbrev digitLaw (ι D : Type*) [Fintype ι] [Fintype D] [Nonempty D] [MeasurableSpace D] :
    Measure (ι → D) :=
  Measure.pi fun _ : ι => (PMF.uniformOfFintype D).toMeasure

/-- The law of a function of one of the independent uniform digits. -/
lemma map_digitLaw_coord {β : Type*} [MeasurableSpace β] (i : ι) {g : D → β}
    (hg : Measurable g) :
    Measure.map (fun r : ι → D => g (r i)) (digitLaw ι D) =
      Measure.map g (PMF.uniformOfFintype D).toMeasure := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := Measure.map_map (μ := digitLaw ι D) hg h.measurable
  rw [h.map_eq] at h1
  exact h1.symm

variable [MeasurableSingletonClass D]

/-- The uniform law on a finite set is invariant under permutations. -/
lemma map_equiv_uniform (e : D ≃ D) :
    (PMF.uniformOfFintype D).toMeasure.map e = (PMF.uniformOfFintype D).toMeasure := by
  refine Measure.ext_of_singleton fun a => ?_
  have hpre : e ⁻¹' {a} = {e.symm a} := by
    ext d
    simp [Equiv.eq_symm_apply]
  rw [Measure.map_apply .of_discrete (measurableSet_singleton a), hpre,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- Independent uniform digits are jointly uniform: the product of the uniform laws on `D` is
the uniform law on `ι → D`. -/
lemma digitLaw_eq_uniform [DecidableEq ι] :
    digitLaw ι D = (PMF.uniformOfFintype (ι → D)).toMeasure := by
  refine Measure.ext_of_singleton fun r => ?_
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton r),
    PMF.uniformOfFintype_apply]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]

/-- For independent uniform digits the expectation is the finite average. -/
lemma integral_digitLaw [DecidableEq ι] (f : (ι → D) → ℝ) :
    ∫ r, f r ∂digitLaw ι D = finAvg f := by
  rw [digitLaw_eq_uniform, integral_uniform_eq_finAvg]

/-- The expectation of a function of one of the independent uniform digits. -/
lemma integral_digitLaw_coord (i : ι) (g : D → ℝ) :
    ∫ r, g (r i) ∂digitLaw ι D = finAvg g := by
  have h := measurePreserving_eval (fun _ : ι => (PMF.uniformOfFintype D).toMeasure) i
  have h1 := integral_map h.aemeasurable (f := g) (Measurable.of_discrete.aestronglyMeasurable)
  rw [h.map_eq, integral_uniform_eq_finAvg] at h1
  exact h1.symm

/-- A function of one of the independent uniform digits that is negated by a permutation of
the digits is symmetric. -/
lemma identDistrib_coord_neg (i : ι) (g : D → ℝ) (φ : D ≃ D) (hφ : ∀ d, g (φ d) = -g d) :
    IdentDistrib (fun r : ι → D => g (r i)) (fun r => -g (r i)) (digitLaw ι D)
      (digitLaw ι D) := by
  have hg : Measurable g := .of_discrete
  have hng : Measurable fun d => -g d := .of_discrete
  have e : (fun d => -g d) = g ∘ φ := by
    funext d
    exact (hφ d).symm
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable,
    (hng.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  rw [map_digitLaw_coord i hg, map_digitLaw_coord i hng, e,
    ← Measure.map_map hg .of_discrete, map_equiv_uniform]

end Uniform

/-- **Fact 2.2 for functions of independent uniform digits.** The probability space is the
finite product `ι → D` with the uniform law (`Oscillation.finAvg` is the expectation),
`X_i = x_i(r_i)` is a function of the `i`-th digit, and the symmetry of `X_i` is witnessed
by a permutation `φ_i` of the digits with `x_i ∘ φ_i = -x_i`. This is an instance of
`fact_2_2_general`. -/
theorem fact_2_2_uniform {ι D : Type*} [Fintype ι] [DecidableEq ι] [Fintype D] [Nonempty D]
    (x : ι → D → ℝ) (φ : ι → D ≃ D) (hφ : ∀ i d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ i, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4) (θ : ℝ) :
    σ * Real.sqrt (Fintype.card ι / 3) ≤ finAvg (fun r : ι → D => |θ + ∑ i, x i (r i)|) := by
  -- the digits carry the discrete σ-algebra, and `ι → D` the law of independent uniform digits
  let _ : MeasurableSpace D := ⊤
  have h := fact_2_2_general (μ := digitLaw ι D) (fun i r => x i (r i))
    (iIndepFun_pi (X := x) fun _ => Measurable.of_discrete.aemeasurable)
    (fun i => identDistrib_coord_neg i (x i) (φ i) (hφ i)) hσ
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 2).trans (h2 i))
    (fun _ => Integrable.of_finite)
    (fun i => (integral_digitLaw_coord i fun d => x i d ^ 4).trans_le (h4 i)) θ
  rwa [integral_digitLaw] at h

end

end R56Audit
end

section
/-!
# Fact 2.2 of the manuscript, in the form used by Lemma 2.3

Auditor's supplement (not part of the audited archive).

**Fact 2.2.** Let `X_1, …, X_m` be independent symmetric random variables with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`. Then `E|θ + X_1 + ⋯ + X_m| ≥ σ √(m/3)` for every real `θ`.

The fact itself, for real random variables on any probability space, is `fact_2_2_general`
in `SymmetricSumsGeneral.lean`. This file states it in the setting of Lemma 2.3: the
probability space is a finite product `Fin n → D` with the uniform law (`D` is the set of
digits, and `Oscillation.finAvg` is the expectation), `X_i = x_i(r_i)` is a function of the
`i`-th digit, and "symmetric" is witnessed by a permutation `φ_i` of the digits with
`x_i ∘ φ_i = -x_i` (`exists_symm_perm_iff`: this is exactly symmetry of the distribution).

* `symmetric_sum_abs`: the sum runs over the points of a set `S`, and the shift `θ` may
  depend on the digits of the other points: the conditioning step of the proof of Lemma 2.3
  ("condition on the children of all other points"). Proved from `fact_2_2_uniform`, the
  instance of `fact_2_2_general` for independent uniform digits, applied for every value of
  the other digits.
* `fact_2_2`: the case of a constant shift.
* `finAvg_mul_coord`, `finAvg_coord`, `finAvg_eq_zero_of_symm`: a digit is uniform and
  independent of the other digits; a symmetric function of a digit has mean zero (used for
  display (7)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ} {D : Type*} [Fintype D]

/-! ### The uniform law on a finite product: one coordinate is independent of the others -/

/-- `(r, d) ↦ (r with r_i := d, r_i)` is an involution of `(Fin n → D) × D`. -/
def updateEquiv (i : Fin n) : ((Fin n → D) × D) ≃ ((Fin n → D) × D) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    rcases p with ⟨r, d⟩
    simp
  right_inv p := by
    rcases p with ⟨r, d⟩
    simp

/-- Resampling one coordinate does not change an average. -/
lemma finAvg_update [Nonempty D] (i : Fin n) (F : (Fin n → D) → ℝ) :
    finAvg (fun r => finAvg (fun d => F (Function.update r i d))) = finAvg F := by
  have h1 := finAvg_prod (fun p : (Fin n → D) × D => F (Function.update p.1 i p.2))
  have h2 := finAvg_equiv (updateEquiv i) (fun p : (Fin n → D) × D => F p.1)
  have h3 := finAvg_prod (fun p : (Fin n → D) × D => F p.1)
  have h4 : finAvg (fun r : Fin n → D => finAvg (fun _ : D => F r)) = finAvg F :=
    finAvg_congr fun r => finAvg_const _
  rw [← h1]
  exact h2.trans (h3.trans h4)

/-- A function of the `i`-th digit is independent of a function that does not depend on
it. -/
lemma finAvg_mul_coord [Nonempty D] (i : Fin n) (g : D → ℝ) (Y : (Fin n → D) → ℝ)
    (hY : ∀ r d, Y (Function.update r i d) = Y r) :
    finAvg (fun r => g (r i) * Y r) = finAvg g * finAvg Y := by
  rw [← finAvg_update i]
  simp only [Function.update_self, hY]
  simp_rw [finAvg_mul_const]
  rw [finAvg_const_mul]

/-- The `i`-th digit is uniform. -/
lemma finAvg_coord [Nonempty D] (i : Fin n) (g : D → ℝ) :
    finAvg (fun r : Fin n → D => g (r i)) = finAvg g := by
  have h := finAvg_mul_coord i g (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa using h

lemma finAvg_neg' {α : Type*} [Fintype α] (f : α → ℝ) :
    finAvg (fun x => -f x) = -finAvg f := by
  have := finAvg_const_mul (-1) f
  simpa using this

/-- A symmetric function of a uniform digit has mean zero. -/
lemma finAvg_eq_zero_of_symm (φ : D ≃ D) (g : D → ℝ) (h : ∀ d, g (φ d) = -g d) :
    finAvg g = 0 := by
  have h1 := finAvg_equiv φ g
  simp only [h] at h1
  rw [finAvg_neg'] at h1
  linarith

/-! ### Sums of independent symmetric jumps -/

/-- `Σ_{i ∈ S} x_i(r_i)`: the sum of the jumps of the points in `S`. -/
def jumpSum (S : Finset (Fin n)) (x : Fin n → D → ℝ) (r : Fin n → D) : ℝ :=
  ∑ i ∈ S, x i (r i)

/-- The digits of the points of `S` and the digits of the other points. -/
def splitDigits (S : Finset (Fin n)) (D : Type*) :
    (Fin n → D) ≃ ({i // i ∈ S} → D) × ({i // i ∉ S} → D) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ S) (fun _ => D)

omit [Fintype D] in
lemma splitDigits_symm_mem (S : Finset (Fin n)) (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D))
    (i : {i // i ∈ S}) : (splitDigits S D).symm p i = p.1 i := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, i.2]

omit [Fintype D] in
lemma splitDigits_symm_notMem (S : Finset (Fin n))
    (p : ({i // i ∈ S} → D) × ({i // i ∉ S} → D)) {i : Fin n} (hi : i ∉ S) :
    (splitDigits S D).symm p i = p.2 ⟨i, hi⟩ := by
  simp [splitDigits, Equiv.piEquivPiSubtypeProd, hi]

/-- **Fact 2.2 (sums of symmetric variables)**, in the form in which Lemma 2.3 uses it: the
jumps `X_i = x_i(r_i)`, `i ∈ S`, are functions of independent uniform digits, and the shift
`θ` may depend on the digits of the other points. If the jumps are symmetric with
`E X_i² = σ²` and `E X_i⁴ ≤ 3σ⁴`, then `E|θ + Σ_{i ∈ S} X_i| ≥ σ √(m/3)`, where `m = |S|`.

"Now condition on the children of all other points \[…\]. This fixes \[…\] the number `θ`.
The children of the `m_R` points of `R^in` are independent of the conditioning, so the jumps
in `D` are still independent and symmetric. \[…\] So Fact 2.2 applies to `θ + D`, with
`m = m_R`." The proof does exactly this: for every value of the other digits, it applies
`fact_2_2_uniform`, the instance of Fact 2.2 (`fact_2_2_general`) for independent uniform
digits. -/
theorem symmetric_sum_abs [Nonempty D] (S : Finset (Fin n)) (x : Fin n → D → ℝ)
    (φ : Fin n → D ≃ D) (hφ : ∀ i ∈ S, ∀ d, x i (φ i d) = -x i d) {σ : ℝ} (hσ : 0 ≤ σ)
    (h2 : ∀ i ∈ S, finAvg (fun d => x i d ^ 2) = σ ^ 2)
    (h4 : ∀ i ∈ S, finAvg (fun d => x i d ^ 4) ≤ 3 * σ ^ 4)
    (θ : (Fin n → D) → ℝ)
    (hθ : ∀ r r' : Fin n → D, (∀ i, i ∉ S → r i = r' i) → θ r = θ r') :
    σ * Real.sqrt (S.card / 3) ≤ finAvg (fun r : Fin n → D => |θ r + jumpSum S x r|) := by
  classical
  rcases hσ.eq_or_lt with rfl | hσpos
  · rw [zero_mul]
    exact finAvg_nonneg fun _ => abs_nonneg _
  -- condition on the digits of the points outside `S`
  rw [← finAvg_equiv (splitDigits S D).symm, finAvg_prod, finAvg_finAvg_comm]
  have hne : Nonempty ({i // i ∉ S} → D) := ⟨fun _ => Classical.arbitrary D⟩
  refine le_trans (le_of_eq (finAvg_const (α := {i // i ∉ S} → D) _).symm) (finAvg_mono fun rO => ?_)
  -- the shift is now a number
  have hconst : ∀ rS : {i // i ∈ S} → D,
      θ ((splitDigits S D).symm (rS, rO)) =
        θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)) := fun rS =>
    hθ _ _ fun i hi => by rw [splitDigits_symm_notMem S _ hi, splitDigits_symm_notMem S _ hi]
  have hsum : ∀ rS : {i // i ∈ S} → D,
      jumpSum S x ((splitDigits S D).symm (rS, rO)) = ∑ i : {i // i ∈ S}, x i (rS i) := by
    intro rS
    unfold jumpSum
    rw [← Finset.sum_coe_sort S (fun i => x i ((splitDigits S D).symm (rS, rO) i))]
    exact Finset.sum_congr rfl fun i _ => by rw [splitDigits_symm_mem]
  -- Fact 2.2 for the digits of the points of `S`
  have hF := fact_2_2_uniform (fun i : {i // i ∈ S} => x i) (fun i : {i // i ∈ S} => φ i)
    (fun i d => hφ i i.2 d) hσpos (fun i => h2 i i.2) (fun i => h4 i i.2)
    (θ ((splitDigits S D).symm (fun _ => Classical.arbitrary D, rO)))
  rw [Fintype.card_coe] at hF
  refine hF.trans (le_of_eq (finAvg_congr fun rS => ?_))
  rw [hconst rS, hsum rS]

end

end R56Audit
end

section
/-!
# Lemma 2.3 of the manuscript (local gain), as stated: every integer base, continuous heights

Auditor's supplement (not part of the audited archive).

**The local experiment** (Section 2.3). Fix one rectangle `R = I × J`. All colors `χ_i`, all
heights `V_i`, and the position of every point relative to `I` (to the left of `I`, in `I`,
or to the right of `I`) are fixed. Each point in `I` falls into one of the children
`C_1, …, C_b` of `I`, uniformly at random and independently of the other points.

Here the data are `ε : Fin n → ℝ` with `|ε i| = 1` (the colors), `V : Fin n → ℝ` (the
heights), `side : Fin n → Side` (the positions relative to `I`), and the outcome of the
experiment is `r : Fin n → Fin b`: the point `i`, if it lies in `I`, falls into the child
`C_{r i + 1}`. The digits of the points outside `I` are present in the sample space but
nothing depends on them (`childAvg_congr`). The expectation is the uniform average
`Oscillation.finAvg` over `r`.

| Manuscript | Here |
| --- | --- |
| weight `w_i` of `P_i` in `I`: `1`, `1/2`, `0` | `oldWeight (side i)` |
| `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}`, display (2) | `endpointAvg ε V side y` |
| child function `a_k` | `childAvg ε V side r k` |
| their average `ā(y) = (1/b) Σ_k a_k(y)` | `childMean ε V side r y` |
| `J`, cut into blocks `B_1, …, B_b` | `Set.Ico s (s + b * L)`, `block s L ℓ` for `ℓ < b` |
| the points of `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})` | `S = innerPoints b V side s L` |
| their number `m_R` | `S.card` |
| jump `X_i = χ_i (b + 1 - 2r) / (2b)` | `jump b ε i d`, with `d = r - 1` |
| `D`, the sum of the jumps of the points of `R^in` | `jumpSum S (jump b ε) r` |
| `g`, "the function `ā` without these jumps" | `withoutJumps b ε V side S r` |

`mem_innerPoints_iff` shows that `innerPoints` consists of the points of `I` whose height
lies in `B_2 ∪ ⋯ ∪ B_{b-1}`.

`local_gain` is **Lemma 2.3**: in the local experiment,

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + (1/4) √(m_R)`.

The proof is the manuscript's, in its four steps. Every display of the proof is stated in
this file, except for one expression in Step 2, which occurs in a proof only. The list says
which definition or statement is which display. Where a display is a chain of relations, the
list says which statement is which link of the chain, or that the statement is the relation
between the two ends of the chain.

* **Step 1: averaging the children.** The first display defines `ā`: it is the definition
  `childMean`. The triangle inequality (`card_mul_osc_avg_le`) and Lemma 2.1
  (`vertical_comparison`), applied to `f = ā`, give display (5): `display_5`.
* **Step 2: the weights in `ā`.** `sum_childWeight` is the display on the weight of a point
  in `ā`: for a point of `I` in the child `C_r`, this weight is the right-hand side
  `1/2 + (b + 1 - 2r) / (2b)` of the display, the old weight `1/2` plus a deviation (and a
  point outside `I` keeps its old weight). The left-hand side `((b - r) + 1/2) / b` of the
  display is a step of the proof of `sum_childWeight`, not a statement. Display (6) is
  `display_6`; `childMean_eq` is the same statement with the right-hand side written as one
  step function. The jumps are symmetric (`jump_rev`), and this gives display (7):
  `finAvg_childMean`.
* **Step 3: taking expectations.** `osc_endpointAvg_le` is the display
  `E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,
  stated as the inequality `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` between its two ends: the two
  equalities hold by the definition of `osc` and the linearity of `E`, and the inequality in
  the middle is `maxOn_endpointAvg_le` and `finAvg_minOn_childMean_le`. Taking expectations
  in (5) gives display (8): `display_8`.
* **Step 4: the gain.** `withoutJumps_eq` is the display that defines `g`, and `offset_eq` is
  the display `mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`. In
  the rest of the step `r = d + 1` is the index of the child and `σ² = (b² - 1) / (12 b²)`.
  * The sentences before the next display: `jump_sq_eq` is `X_i² = (r - (b+1)/2)² / b²`;
    `finAvg_childIndex` and `finAvg_childIndex_sq` are the mean `(b+1)/2` and the second
    moment `(b+1)(2b+1)/6` of `r`; `finAvg_childIndex_var` is its variance,
    `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12` (both equalities); and `abs_jump_le` is
    `|X_i| ≤ (b-1)/(2b)`.
  * The display on the moments of the jumps: `finAvg_jump_sq` is `E X_i² = σ²`. The chain
    `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴` is `finAvg_jump_fourth_le_sq` (its
    first inequality) and `sq_mul_sigma_sq_le` (its second inequality and its equality);
    `finAvg_jump_fourth_le` is the inequality `E X_i⁴ ≤ 3σ⁴` between its two ends.
  * The last display,
    `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`:
    `expected_offset_ge_sigma` is its first inequality, by Fact 2.2 (`symmetric_sum_abs`, an
    application of `fact_2_2_general`); `sigma_mul_sqrt_eq` is its equality;
    `sqrt_sq_sub_one_div_ge` is its last inequality; `sqrt_div_eight_le` is the equality and
    the last inequality together, `σ √(m/3) ≥ √m / 8`; and `expected_offset_ge` is the
    inequality between the two ends of the display.

"Together with (8), this proves the inequality of the lemma": `local_gain` is proved from
`display_8` and `expected_offset_ge`.

**Blocks of an interval, and arbitrary sets of heights.** `display_5`, `display_8`,
`offset_eq`, `expected_offset_ge_sigma` and `expected_offset_ge` are stated as in the
manuscript, for the blocks `B_1, …, B_b` of an interval `J` and the points of `R^in`. The
first four are proved from statements of the same form for sets of heights in place of the
blocks:

* `display_5` from `avg_comparison_core`, and `display_8` from `expected_comparison_core`
  (which is proved from `avg_comparison_core` and `osc_endpointAvg_le`). These two are stated
  for nonempty subsets `B_1, …, B_b` of a set `J` of heights, with the inequality of
  Lemma 2.1 as a hypothesis; for the blocks of an interval this hypothesis is
  `vertical_comparison`.
* `offset_eq` from `offset_core`, and `expected_offset_ge_sigma` from
  `expected_offset_core_sigma` (which is proved from `offset_core` and Fact 2.2). These two
  are stated for nonempty sets `B_1, …, B_b` of heights and a set `S` of points of `I` whose
  heights lie above all of `B_1` and at or below all of `B_b`; for the blocks of an interval
  and the points of `R^in` this hypothesis is `innerPoints_between_blocks`.

`expected_offset_ge` is proved from `expected_offset_ge_sigma` and `sqrt_div_eight_le`. In
the same way `expected_offset_core`, the same inequality for sets of heights, is proved from
`expected_offset_core_sigma` and `sqrt_div_eight_le`. Display (6) does not involve the
blocks: `display_6` is proved from `childMean_eq`.

So the same steps serve for intervals and for sampled heights: `local_gain_core`, proved
from `expected_comparison_core` and `expected_offset_core`, and `local_gain_sets` are
Lemma 2.3 in this generality.

`EndpointAverage.lean` proves that `endpointAvg` and `childAvg` are the endpoint averages
`(F(I⁻, y) + F(I⁺, y)) / 2` of `I` and of its children (first equality of display (2)).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Step functions of the height -/

/-- The function `y ↦ Σ_i c_i 1{V_i ≤ y}` of the height. The manuscript's functions of the
height are of this form up to an additive constant; those of Lemma 2.3 (`endpointAvg`,
`childAvg` and their average) are exactly of this form. -/
def stepFn (V : Fin n → ℝ) (c : Fin n → ℝ) (y : ℝ) : ℝ := ∑ i, if V i ≤ y then c i else 0

lemma stepFn_add (V c c' : Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => c i + c' i) y = stepFn V c y + stepFn V c' y := by
  unfold stepFn
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_sum {ι : Type*} (s : Finset ι) (V : Fin n → ℝ) (c : ι → Fin n → ℝ) (y : ℝ) :
    stepFn V (fun i => ∑ k ∈ s, c k i) y = ∑ k ∈ s, stepFn V (c k) y := by
  unfold stepFn
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_div (V c : Fin n → ℝ) (t : ℝ) (y : ℝ) :
    stepFn V (fun i => c i / t) y = stepFn V c y / t := by
  unfold stepFn
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma stepFn_congr (V : Fin n → ℝ) {c c' : Fin n → ℝ} (h : ∀ i, c i = c' i) (y : ℝ) :
    stepFn V c y = stepFn V c' y := by
  unfold stepFn
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- "They take finitely many values". -/
lemma stepFn_image_finite (V c : Fin n → ℝ) (B : Set ℝ) : ((stepFn V c) '' B).Finite := by
  classical
  refine (Set.finite_range (fun T : Finset (Fin n) => ∑ i ∈ T, c i)).subset ?_
  rintro _ ⟨y, -, rfl⟩
  refine ⟨Finset.univ.filter (fun i => V i ≤ y), ?_⟩
  simp only [stepFn]
  rw [Finset.sum_filter]

/-- Below all the heights that carry a nonzero coefficient, the function vanishes. -/
lemma stepFn_eq_zero (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → y < V i) :
    stepFn V c y = 0 := by
  unfold stepFn
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · by_contra hc
    exact absurd hi (not_le.mpr (h i hc))
  · rfl

/-- Above all the heights that carry a nonzero coefficient, the function is the sum of the
coefficients. -/
lemma stepFn_eq_sum (V : Fin n → ℝ) {c : Fin n → ℝ} {y : ℝ} (h : ∀ i, c i ≠ 0 → V i ≤ y) :
    stepFn V c y = ∑ i, c i := by
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · by_contra hc
    exact hi (h i (fun h0 => hc (by rw [h0])))

lemma finAvg_stepFn {α : Type*} [Fintype α] [Nonempty α] (V : Fin n → ℝ) (c : α → Fin n → ℝ)
    (y : ℝ) :
    finAvg (fun r => stepFn V (c r) y) = stepFn V (fun i => finAvg (fun r => c r i)) y := by
  unfold stepFn
  rw [finAvg_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · exact finAvg_const 0

/-! ### The local experiment -/

/-- The position of a point relative to the horizontal interval `I`. -/
inductive Side
  | left
  | inside
  | right
  deriving DecidableEq

/-- The weight `w_i` of a point in `I`: `1` to the left of `I`, `1/2` in `I`, `0` to the
right of `I`. -/
def oldWeight : Side → ℝ
  | .left => 1
  | .inside => 1 / 2
  | .right => 0

/-- The weight of a point in the child `C_{k+1}` of `I`. A point outside `I` lies on the same
side of every child. A point of `I` in the child `C_{r+1}` lies to the left of `C_{k+1}` if
`r < k`, in it if `r = k`, and to the right of it if `r > k`. -/
def childWeight {b : ℕ} (sd : Side) (r k : Fin b) : ℝ :=
  match sd with
  | .left => 1
  | .inside => if r < k then 1 else if r = k then 1 / 2 else 0
  | .right => 0

/-- The endpoint average `a(y) = Σ_i χ_i w_i 1{V_i ≤ y}` of `I`, display (2): the old
function. -/
def endpointAvg (ε V : Fin n → ℝ) (side : Fin n → Side) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i))

/-- The endpoint average `a_{k+1}` of the child `C_{k+1}`: a child function. -/
def childAvg {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b)
    (k : Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * childWeight (side i) (r i) k)

/-- The points of the inner region `R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`: the points of `I` whose
height lies in `[s + L, s + (b-1) L)`. -/
def innerPoints (b : ℕ) (V : Fin n → ℝ) (side : Fin n → Side) (s L : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L)

/-! ### Step 1: averaging the children -/

/-- `ā`: the average of the child functions, `ā(y) = (1/b) Σ_k a_k(y)`. -/
def childMean {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side) (r : Fin n → Fin b) : ℝ → ℝ :=
  fun y => (∑ k : Fin b, childAvg ε V side r k y) / b

/-- "They take finitely many values": `ā` is a step function of the height, like the child
functions. -/
lemma childMean_image_finite {b : ℕ} (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (A : Set ℝ) : ((childMean ε V side r) '' A).Finite := by
  have h : childMean ε V side r =
      stepFn V (fun i => (∑ k : Fin b, ε i * childWeight (side i) (r i) k) / b) := by
    funext y
    unfold childMean childAvg
    rw [stepFn_div, stepFn_sum]
  rw [h]
  exact stepFn_image_finite V _ A

/-- **Display (5)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`): for every outcome of the local
experiment,

`Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} ā + 2 |mid_{B_b} ā - mid_{B_1} ā|`.

`display_5` is the case of the blocks of an interval. -/
theorem avg_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f)
    (r : Fin n → Fin b) :
    ∑ ℓ : Fin b, osc (B ℓ) (childMean ε V side r) +
        2 * |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)| ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  have hJ : J.Nonempty := (hne ⟨0, hb0⟩).mono (hsub ⟨0, hb0⟩)
  -- "By the triangle inequality for the oscillation,
  -- `Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`."
  have h1 : (b : ℝ) * osc J (childMean ε V side r) ≤
      ∑ k : Fin b, osc J (childAvg ε V side r k) := by
    have h := card_mul_osc_avg_le (ι := Fin b) (B := J)
      (f := fun k => childAvg ε V side r k) hJ (fun k => stepFn_image_finite V _ _)
    rw [Fintype.card_fin] at h
    exact h
  -- "So Lemma 2.1, applied to `f = ā`, gives" display (5)
  exact (hcomp _ (childMean_image_finite ε V side r J)).trans h1

/-! ### Step 2: the weights in `ā` -/

/-- "So its weight in `ā` is `((b - r) + 1/2) / b = 1/2 + (b + 1 - 2r) / (2b)`": the average
over the `b` children of the weight of a point is its old weight plus a deviation, which
vanishes for points outside `I`. -/
lemma sum_childWeight {b : ℕ} (hb : 0 < b) (sd : Side) (r : Fin b) :
    (∑ k : Fin b, childWeight sd r k) / b =
      oldWeight sd + (if sd = Side.inside then ((b : ℝ) - 1 - 2 * (r : ℕ)) / (2 * b) else 0) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  cases sd with
  | left =>
    simp only [childWeight, oldWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, reduceCtorEq, ite_false, add_zero]
    field_simp
  | right =>
    simp [childWeight, oldWeight]
  | inside =>
    simp only [childWeight, oldWeight, ite_true]
    have hsplit : ∀ k : Fin b, (if r < k then (1 : ℝ) else if r = k then 1 / 2 else 0) =
        (if r < k then (1 : ℝ) else 0) + (if r = k then 1 / 2 else 0) := by
      intro k
      by_cases h1 : r < k
      · have h2 : r ≠ k := ne_of_lt h1
        simp [h1, h2]
      · simp [h1]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ r (fun _ => (1 / 2 : ℝ)),
      ite_eq_left (Finset.mem_univ r), Finset.sum_boole]
    have hcard : (Finset.univ.filter (fun k : Fin b => r < k)).card = b - 1 - r := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hcard]
    have hr : (r : ℕ) + 1 ≤ b := r.isLt
    have hcast : ((b - 1 - (r : ℕ) : ℕ) : ℝ) = (b : ℝ) - 1 - (r : ℕ) := by
      have h : (b - 1 - (r : ℕ)) + (r : ℕ) + 1 = b := by omega
      have h' := congrArg (Nat.cast : ℕ → ℝ) h
      push_cast at h'
      linarith
    rw [hcast]
    field_simp
    ring

/-- The jump `X_i = χ_i (b + 1 - 2r) / (2b)` of a point of `I` in the child `C_r`, written
with `d = r - 1 ∈ {0, …, b-1}`: the deviation of its weight in `ā` from its old weight `1/2`,
multiplied by its color. -/
def jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) : ℝ :=
  ε i * (((b : ℝ) - 1 - 2 * (d : ℕ)) / (2 * b))

/-- Display (6) with its right-hand side written as one step function,
`ā(y) = Σ_i (χ_i w_i + 1{U_i ∈ I} X_i) 1{V_i ≤ y}`: the function `ā` "counts each point with
the average of its weights in the `b` children", which is its old weight for a point outside
`I` and "its old weight `1/2` plus a deviation" for a point in `I`. See `display_6` for the
manuscript's form. -/
lemma childMean_eq {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y =
      stepFn V (fun i => ε i * oldWeight (side i) +
        (if side i = Side.inside then jump b ε i (r i) else 0)) y := by
  unfold childMean childAvg
  rw [← stepFn_sum, ← stepFn_div]
  refine stepFn_congr V (fun i => ?_) y
  rw [← Finset.mul_sum, mul_div_assoc, sum_childWeight hb, mul_add]
  unfold jump
  split_ifs <;> ring

/-- "So `b + 1 - 2r` is uniform on the symmetric set `{1 - b, 3 - b, …, b - 1}`, and the `X_i`
are independent and symmetric, whatever the colors are": reversing the order of the children
changes the sign of the jump. -/
lemma jump_rev (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) (d : Fin b) :
    jump b ε i (Fin.revPerm d) = -jump b ε i d := by
  have hd : (d : ℕ) + 1 ≤ b := d.isLt
  have hcast : (((Fin.rev d : Fin b) : ℕ) : ℝ) = (b : ℝ) - 1 - (d : ℕ) := by
    rw [Fin.val_rev]
    have h : (b - ((d : ℕ) + 1)) + (d : ℕ) + 1 = b := by omega
    have h' := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h'
    linarith
  unfold jump
  rw [Fin.revPerm_apply, hcast]
  ring

/-- "In particular `E X_i = 0`", because the jumps are symmetric. -/
lemma finAvg_jump (b : ℕ) (ε : Fin n → ℝ) (i : Fin n) : finAvg (jump b ε i) = 0 :=
  finAvg_eq_zero_of_symm Fin.revPerm (jump b ε i) (jump_rev b ε i)

/-- **Display (7)**: "In particular `E X_i = 0`, and (6) gives"

`E ā(y) = a(y)` "for every height `y`". -/
lemma finAvg_childMean {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side) (y : ℝ) :
    finAvg (fun r : Fin n → Fin b => childMean ε V side r y) = endpointAvg ε V side y := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  simp_rw [childMean_eq hb]
  rw [finAvg_stepFn]
  unfold endpointAvg
  refine stepFn_congr V (fun i => ?_) y
  rw [finAvg_add, finAvg_const]
  by_cases hs : side i = Side.inside
  · -- the jump of a point in `I` has expectation zero
    simp only [hs, ite_true]
    rw [finAvg_coord i (jump b ε i), finAvg_jump, add_zero]
  · simp only [hs, ite_false]
    rw [finAvg_const, add_zero]

/-! ### Step 3: taking expectations -/

/-- "The expectation of a maximum is at least the maximum of the expectations": by display
(7), `E max_B ā ≥ max_B a` for every nonempty set `B` of heights. -/
lemma maxOn_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    maxOn B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => maxOn B (childMean ε V side r)) := by
  apply maxOn_le hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => le_maxOn (childMean_image_finite ε V side r B) hy

/-- "\[…\] and the expectation of a minimum is at most the minimum of the expectations": by
display (7), `E min_B ā ≤ min_B a` for every nonempty set `B` of heights. -/
lemma finAvg_minOn_childMean_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    finAvg (fun r : Fin n → Fin b => minOn B (childMean ε V side r)) ≤
      minOn B (endpointAvg ε V side) := by
  apply le_minOn hB
  intro y hy
  rw [← finAvg_childMean hb ε V side y]
  exact finAvg_mono fun r => minOn_le (childMean_image_finite ε V side r B) hy

/-- "So (7) gives, for every `ℓ`,"

`E osc_{B_ℓ} ā = E max_{B_ℓ} ā - E min_{B_ℓ} ā ≥ max_{B_ℓ} a - min_{B_ℓ} a = osc_{B_ℓ} a`,

here for every nonempty set `B` of heights in place of `B_ℓ`. -/
lemma osc_endpointAvg_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) :
    osc B (endpointAvg ε V side) ≤
      finAvg (fun r : Fin n → Fin b => osc B (childMean ε V side r)) := by
  have hmax := maxOn_endpointAvg_le hb ε V side hB
  have hmin := finAvg_minOn_childMean_le hb ε V side hB
  unfold osc
  rw [finAvg_sub]
  linarith

/-- **Display (8)** for subsets `B_1, …, B_b` of a set `J` of heights for which the
inequality of Lemma 2.1 holds (hypothesis `hcomp`):

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

`display_8` is the case of the blocks of an interval. -/
theorem expected_comparison_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (J : Set ℝ) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J)
    (hcomp : ∀ f : ℝ → ℝ, (f '' J).Finite →
      ∑ ℓ : Fin b, osc (B ℓ) f +
          2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f) :
    ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b =>
          |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
            mid (B ⟨0, by omega⟩) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b => ∑ k : Fin b, osc J (childAvg ε V side r k)) := by
  have hb0 : 0 < b := by omega
  -- "Taking expectations in (5)"
  have hE := finAvg_mono (avg_comparison_core hb ε V side J B hne hsub hcomp)
  rw [finAvg_add, finAvg_sum, finAvg_const_mul] at hE
  -- `E osc_{B_ℓ} ā ≥ osc_{B_ℓ} a` for every `ℓ`
  have hblocks : ∑ ℓ : Fin b, osc (B ℓ) (endpointAvg ε V side) ≤
      ∑ ℓ : Fin b, finAvg (fun r : Fin n → Fin b => osc (B ℓ) (childMean ε V side r)) :=
    Finset.sum_le_sum fun ℓ _ => osc_endpointAvg_le hb0 ε V side (hne ℓ)
  linarith

/-- **Display (8).** "Taking expectations in (5), we get"

`E Σ_k osc_J a_k ≥ Σ_ℓ osc_{B_ℓ} a + 2 E|mid_{B_b} ā - mid_{B_1} ā|`.

"The first term on the right is what the horizontal strips had. The second term is the
gain." -/
theorem display_8 {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        2 * finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
          mid (block s L 0) (childMean ε V side r)|) ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) :=
  expected_comparison_core hb ε V side (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt)
    (fun f hf => vertical_comparison hb s hL f hf)

/-! ### Step 4: the gain

In the manuscript `D` is the sum of the jumps of the points of `R^in`, and `g` is `ā` without
these jumps. In the statements below a set `S` of points of `I` takes the place of the set of
the points of `R^in`: `D = jumpSum S (jump b ε) r` (`jumpSum` is defined in
`SymmetricSums.lean`) and `g = withoutJumps b ε V side S r`. -/

/-- `g`: "the function `ā` without these jumps", the jumps of the points of `S`. Like `ā` in
`childMean_eq`, it is written as one step function; see `withoutJumps_eq` for the
manuscript's form. -/
def withoutJumps (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    (r : Fin n → Fin b) : ℝ → ℝ :=
  stepFn V (fun i => ε i * oldWeight (side i) +
    (if side i = Side.inside ∧ i ∉ S then jump b ε i (r i) else 0))

/-- "They take finitely many values": `g` is a step function of the height. -/
lemma withoutJumps_image_finite (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (S : Finset (Fin n)) (r : Fin n → Fin b) (A : Set ℝ) :
    ((withoutJumps b ε V side S r) '' A).Finite :=
  stepFn_image_finite V _ A

/-- "The heights of the points of `R^in` lie above `B_1` and below `B_b`": above every
height of the bottom block `B_1 = block s L 0`, and at or below every height of the top block
`B_b = block s L (b - 1)`. -/
lemma innerPoints_between_blocks {b : ℕ} (hb : 2 ≤ b) (V : Fin n → ℝ) (side : Fin n → Side)
    (s L : ℝ) :
    ∀ i ∈ innerPoints b V side s L, side i = Side.inside ∧
      (∀ y ∈ block s L 0, y < V i) ∧ (∀ y ∈ block s L (b - 1), V i ≤ y) := by
  intro i hi
  have hi' : side i = Side.inside ∧ s + L ≤ V i ∧ V i < s + ((b : ℝ) - 1) * L := by
    simpa [innerPoints] using hi
  refine ⟨hi'.1, fun y hy => ?_, fun y hy => ?_⟩
  · have h2 : y < s + ((0 : ℕ) + 1 : ℝ) * L := hy.2
    simp only [Nat.cast_zero, zero_add, one_mul] at h2
    linarith [hi'.2.1]
  · have h2 : s + ((b - 1 : ℕ) : ℝ) * L ≤ y := hy.1
    rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one] at h2
    linarith [hi'.2.2]

/-- By display (6), `ā` is `g` plus the jumps of the points of `S`, for every set `S` of
points of `I`: `ā(y) = g(y) + Σ_{i ∈ S, V_i ≤ y} X_i`, where the last sum is written as a
step function. -/
lemma childMean_eq_withoutJumps_add {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) (y : ℝ) :
    childMean ε V side r y = withoutJumps b ε V side S r y +
      stepFn V (fun i => if i ∈ S then jump b ε i (r i) else 0) y := by
  rw [childMean_eq hb]
  unfold withoutJumps
  rw [← stepFn_add]
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : i ∈ S
  · simp [hi, hS i hi]
  · simp [hi]

/-- "So by (6), their jumps do not enter `ā` on `B_1`": `ā(y) = g(y)` at every height `y`
below the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_of_lt {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, y < V i) :
    childMean ε V side r y = withoutJumps b ε V side S r y := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_zero, add_zero]
  exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "\[…\] and they add the constant `D` to `ā` on `B_b`": `ā(y) = g(y) + D` at every height
`y` at or above the heights of the points of `S`. -/
lemma childMean_eq_withoutJumps_add_jumpSum_of_le {b : ℕ} (hb : 0 < b) (ε V : Fin n → ℝ)
    (side : Fin n → Side) (S : Finset (Fin n)) (hS : ∀ i ∈ S, side i = Side.inside)
    (r : Fin n → Fin b) {y : ℝ} (hy : ∀ i ∈ S, V i ≤ y) :
    childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r := by
  rw [childMean_eq_withoutJumps_add hb ε V side S hS, stepFn_eq_sum]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, jumpSum]
  · exact fun i hi => hy i (ite_ne_right_iff.mp hi).1

/-- "`mid_{B_b} ā - mid_{B_1} ā = θ + D`, where `θ = mid_{B_b} g - mid_{B_1} g`", for
nonempty sets `B_1, …, B_b` of heights and any set `S` of points of `I` whose heights lie
above all of `B_1` and at or below all of `B_b`. `offset_eq` is the case of the blocks of an
interval and the points of `R^in`. -/
theorem offset_core {b : ℕ} (hb : 2 ≤ b) (ε V : Fin n → ℝ) (side : Fin n → Side)
    (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y))
    (r : Fin n → Fin b) :
    mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
        mid (B ⟨0, by omega⟩) (childMean ε V side r) =
      (mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) +
      jumpSum S (jump b ε) r := by
  have hb0 : 0 < b := by omega
  have hI : ∀ i ∈ S, side i = Side.inside := fun i hi => (hS i hi).1
  -- "That is, `ā = g` on `B_1` and `ā = g + D` on `B_b`."
  have hbot : ∀ y ∈ B ⟨0, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y := fun y hy =>
    childMean_eq_withoutJumps_of_lt hb0 ε V side S hI r fun i hi => (hS i hi).2.1 y hy
  have htop : ∀ y ∈ B ⟨b - 1, by omega⟩,
      childMean ε V side r y = withoutJumps b ε V side S r y + jumpSum S (jump b ε) r :=
    fun y hy => childMean_eq_withoutJumps_add_jumpSum_of_le hb0 ε V side S hI r
      fun i hi => (hS i hi).2.2 y hy
  -- "Adding the constant `D` to a function adds `D` to its midpoint"
  rw [mid_congr hbot, mid_congr htop,
    mid_add_const (hne _) (withoutJumps_image_finite b ε V side S r _)]
  ring

/-- "Now condition on the children of all other points in `I` \[…\]. This fixes the function
`g`": `g` depends on the outcome only through the children of the points of `I` that are
not in `S`. -/
lemma withoutJumps_congr (b : ℕ) (ε V : Fin n → ℝ) (side : Fin n → Side) (S : Finset (Fin n))
    {r r' : Fin n → Fin b} (h : ∀ i, side i = Side.inside → i ∉ S → r i = r' i) :
    withoutJumps b ε V side S r = withoutJumps b ε V side S r' := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  by_cases hi : side i = Side.inside ∧ i ∉ S
  · rw [h i hi.1 hi.2]
  · simp [hi]

/-! ### Step 4: the moments of the jumps

"By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`. Here `r` has
mean `(b+1)/2` and second moment `(b+1)(2b+1)/6`, so its variance is
`(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`. Also `|X_i| ≤ (b-1)/(2b)`." These sentences are
`jump_sq_eq`, then `finAvg_childIndex`, `finAvg_childIndex_sq` and `finAvg_childIndex_var`,
then `abs_jump_le`. In this file the digit `d = r - 1` is uniform on `{0, …, b-1}`, and the
index `r` of the child is written `d + 1`.

The display that follows these sentences,

`E X_i² = (b²-1)/(12b²) =: σ²`,   `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`,

is `finAvg_jump_sq`, then `finAvg_jump_fourth_le_sq` (the first inequality of the chain) and
`sq_mul_sigma_sq_le` (its second inequality and its equality). `finAvg_jump_fourth_le` is
the inequality between the two ends of the chain.

`sum_centered_sq` is the same variance written with the digit `d`:
`X_i² = (b - 1 - 2d)² / (4b²)`, and `(1/b) Σ_d (b - 1 - 2d)² / 4 = (b² - 1) / 12`. The proofs
below do not use it. -/

/-- `Σ_{d=0}^{N-1} d = N (N - 1) / 2`. -/
lemma sum_range_id_real (N : ℕ) : ∑ d ∈ Finset.range N, (d : ℝ) = (N : ℝ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{d=0}^{N-1} d² = N (N - 1) (2N - 1) / 6`. -/
lemma sum_range_sq_real (N : ℕ) :
    ∑ d ∈ Finset.range N, (d : ℝ) ^ 2 = (N : ℝ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- "By definition, `X_i² = (r - (b+1)/2)² / b²`", where `r = d + 1` is the index of the
child: the jump is `X_i = χ_i (b + 1 - 2r) / (2b)`, and `χ_i² = 1`. That `r` is uniform on
`{1, …, b}` is expressed in the next lemmas by the average `finAvg` over the digit `d`. -/
lemma jump_sq_eq {b : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) (d : Fin b) :
    jump b ε i d ^ 2 = ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 / (b : ℝ) ^ 2 := by
  have hε2 : ε i ^ 2 = 1 := by rw [← sq_abs, hε i]; norm_num
  unfold jump
  rw [mul_pow, hε2]
  ring

/-- "Here `r` has mean `(b+1)/2`": the mean of the index `r = d + 1` of the child. -/
lemma finAvg_childIndex {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((d : ℕ) : ℝ) + 1) = ((b : ℝ) + 1) / 2 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r = Σ_{r=0}^{b} r = b (b + 1) / 2`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) = (b : ℝ) * ((b : ℝ) + 1) / 2 := by
    have h := sum_range_id_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => (d : ℝ) + 1) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] and second moment `(b+1)(2b+1)/6`": the mean of `r²` for the index `r = d + 1` of
the child. -/
lemma finAvg_childIndex_sq {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => (((d : ℕ) : ℝ) + 1) ^ 2) = ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  -- `Σ_{r=1}^{b} r² = Σ_{r=0}^{b} r² = b (b + 1) (2b + 1) / 6`
  have hsum : ∑ d : Fin b, (((d : ℕ) : ℝ) + 1) ^ 2 =
      (b : ℝ) * ((b : ℝ) + 1) * (2 * b + 1) / 6 := by
    have h := sum_range_sq_real (b + 1)
    rw [Finset.sum_range_succ'] at h
    push_cast at h
    rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((d : ℝ) + 1) ^ 2) b]
    linarith
  -- divide by the number `b` of children
  unfold finAvg
  rw [hsum, Fintype.card_fin]
  field_simp

/-- "\[…\] so its variance is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`": the variance of the
index `r = d + 1` of the child is its second moment minus the square of its mean (the first
equality), and this number is `(b² - 1) / 12` (the second equality). -/
lemma finAvg_childIndex_var {b : ℕ} (hb : 0 < b) :
    finAvg (fun d : Fin b => ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2) =
        ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 ∧
      ((b : ℝ) + 1) * (2 * b + 1) / 6 - ((b : ℝ) + 1) ^ 2 / 4 = ((b : ℝ) ^ 2 - 1) / 12 := by
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  refine ⟨?_, by ring⟩
  -- `(r - μ)² = r² - 2μ r + μ²` for the mean `μ = (b+1)/2`
  have hexp : ∀ d : Fin b, ((((d : ℕ) : ℝ) + 1) - ((b : ℝ) + 1) / 2) ^ 2 =
      (((d : ℕ) : ℝ) + 1) ^ 2 - ((b : ℝ) + 1) * (((d : ℕ) : ℝ) + 1) + ((b : ℝ) + 1) ^ 2 / 4 :=
    fun d => by ring
  -- take expectations, and use the mean and the second moment of `r`
  rw [finAvg_congr hexp, finAvg_add, finAvg_sub, finAvg_const_mul, finAvg_const,
    finAvg_childIndex_sq hb, finAvg_childIndex hb]
  ring

/-- `E X_i² = (b² - 1) / (12 b²) =: σ²`, the first formula of the display on the moments of
the jumps: `X_i² = (r - (b+1)/2)² / b²` (`jump_sq_eq`), and the variance of `r` is
`(b² - 1) / 12` (`finAvg_childIndex_var`). -/
lemma finAvg_jump_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 2) = ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
  -- "By definition, `X_i² = (r - (b+1)/2)² / b²` with `r` uniform on `{1, …, b}`."
  rw [finAvg_congr (jump_sq_eq ε hε i), finAvg_div_const]
  -- the variance of `r` is `(b+1)(2b+1)/6 - (b+1)²/4 = (b²-1)/12`
  rw [(finAvg_childIndex_var hb).1, (finAvg_childIndex_var hb).2, div_div]

/-- `|X_i| ≤ (b - 1) / (2b)`. -/
lemma abs_jump_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) (i : Fin n)
    (d : Fin b) : |jump b ε i d| ≤ ((b : ℝ) - 1) / (2 * b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hd0 : (0 : ℝ) ≤ (d : ℕ) := Nat.cast_nonneg _
  have hd1 : ((d : ℕ) : ℝ) + 1 ≤ b := by exact_mod_cast d.isLt
  unfold jump
  rw [abs_mul, hε i, one_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * b)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- The first inequality of the chain for the fourth moment, `E X_i⁴ ≤ ((b-1)/(2b))² σ²`,
where `σ² = (b² - 1) / (12 b²)`: `X_i⁴ ≤ ((b-1)/(2b))² X_i²` because `|X_i| ≤ (b-1)/(2b)`
(`abs_jump_le`), and `E X_i² = σ²` (`finAvg_jump_sq`). -/
lemma finAvg_jump_fourth_le_sq {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
  -- `X_i⁴ ≤ ((b-1)/(2b))² X_i²`, because `|X_i| ≤ (b-1)/(2b)`
  have hpt : ∀ d : Fin b, jump b ε i d ^ 4 ≤
      (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 := by
    intro d
    have h1 : jump b ε i d ^ 2 ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_jump_le hb ε hε i d) 2
    have h2 : (0 : ℝ) ≤ jump b ε i d ^ 2 := sq_nonneg _
    calc jump b ε i d ^ 4 = jump b ε i d ^ 2 * jump b ε i d ^ 2 := by ring
      _ ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h2
  -- take expectations, and use `E X_i² = σ²`
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ finAvg (fun d : Fin b => (((b : ℝ) - 1) / (2 * b)) ^ 2 * jump b ε i d ^ 2) :=
        finAvg_mono hpt
    _ = (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) := by
        rw [finAvg_const_mul, finAvg_jump_sq hb ε hε i]

/-- The rest of the chain for the fourth moment,
`((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`. The
inequality holds because `(b - 1)² ≤ b² - 1` for `b ≥ 1` and `σ² ≥ 0`, and the equality
because `(b² - 1) / (4b²) = 3σ²`. -/
lemma sq_mul_sigma_sq_le {b : ℕ} (hb : 0 < b) :
    (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ≤
        ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ∧
      ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) =
        3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  refine ⟨?_, by ring⟩
  -- `σ² ≥ 0`
  have hs : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  -- `((b-1)/(2b))² ≤ (b²-1)/(4b²)`, because `(b - 1)² ≤ b² - 1` for `b ≥ 1`
  have hk : (((b : ℝ) - 1) / (2 * b)) ^ 2 ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) := by
    rw [div_pow, show (2 * (b : ℝ)) ^ 2 = 4 * (b : ℝ) ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  exact mul_le_mul_of_nonneg_right hk hs

/-- `E X_i⁴ ≤ 3σ⁴`, where `σ² = (b² - 1) / (12 b²)`: the inequality between the two ends of
the chain `E X_i⁴ ≤ ((b-1)/(2b))² σ² ≤ ((b²-1)/(4b²)) σ² = 3σ⁴`, whose links are
`finAvg_jump_fourth_le_sq` and `sq_mul_sigma_sq_le`. This is the fourth-moment hypothesis of
Fact 2.2. -/
lemma finAvg_jump_fourth_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (i : Fin n) :
    finAvg (fun d : Fin b => jump b ε i d ^ 4) ≤
      3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 :=
  calc finAvg (fun d : Fin b => jump b ε i d ^ 4)
      ≤ (((b : ℝ) - 1) / (2 * b)) ^ 2 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        finAvg_jump_fourth_le_sq hb ε hε i
    _ ≤ ((b : ℝ) ^ 2 - 1) / (4 * (b : ℝ) ^ 2) * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) :=
        (sq_mul_sigma_sq_le hb).1
    _ = 3 * (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := (sq_mul_sigma_sq_le hb).2

/-! ### Step 4: the last display

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

where `σ² = (b² - 1) / (12 b²)`. The first inequality is `expected_offset_ge_sigma`, the
equality is `sigma_mul_sqrt_eq`, the last inequality is `sqrt_sq_sub_one_div_ge`, and
`expected_offset_ge` is the inequality between the two ends of the display.
`sqrt_div_eight_le` is the equality and the last inequality together. -/

/-- The equality of the last display, `σ √(m/3) = (√(b² - 1) / (6b)) √m`, where
`σ² = (b² - 1) / (12 b²)`. -/
lemma sigma_mul_sqrt_eq {b : ℕ} (hb : 0 < b) (m : ℕ) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) =
      Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnum : (0 : ℝ) ≤ (b : ℝ) ^ 2 - 1 := by nlinarith
  -- `√(12 b²) √3 = √(36 b²) = 6b`
  have h6 : Real.sqrt (12 * (b : ℝ) ^ 2) * Real.sqrt 3 = 6 * b := by
    rw [← Real.sqrt_mul (by positivity), show 12 * (b : ℝ) ^ 2 * 3 = (6 * b) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  -- `σ = √(b² - 1) / √(12 b²)` and `√(m/3) = √m / √3`
  rw [Real.sqrt_div hnum, Real.sqrt_div (Nat.cast_nonneg m), div_mul_div_comm, h6]
  ring

/-- The last inequality of the last display, `(√(b² - 1) / (6b)) √m ≥ √m / 8`, "because
`16 (b² - 1) ≥ 9 b²` for `b ≥ 2`". -/
lemma sqrt_sq_sub_one_div_ge {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  -- "because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`"
  have h16 : 9 * (b : ℝ) ^ 2 ≤ 16 * ((b : ℝ) ^ 2 - 1) := by nlinarith
  -- so `3b/4 ≤ √(b² - 1)`, that is, `1/8 ≤ √(b² - 1) / (6b)`
  have h34 : 3 * (b : ℝ) / 4 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) := by
    apply Real.le_sqrt_of_sq_le
    linarith [show (3 * (b : ℝ) / 4) ^ 2 = 9 * (b : ℝ) ^ 2 / 16 by ring]
  have hc : (1 : ℝ) / 8 ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- multiply by `√m ≥ 0`
  calc Real.sqrt m / 8 = 1 / 8 * Real.sqrt m := by ring
    _ ≤ Real.sqrt ((b : ℝ) ^ 2 - 1) / (6 * b) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

/-- `σ √(m/3) ≥ √m / 8` for `σ² = (b² - 1) / (12 b²)` and `b ≥ 2`: the equality and the last
inequality of the last display together (`sigma_mul_sqrt_eq`, `sqrt_sq_sub_one_div_ge`). -/
lemma sqrt_div_eight_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Real.sqrt m / 8 ≤
      Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (m / 3) := by
  -- `σ √(m/3) = (√(b² - 1) / (6b)) √m`
  rw [sigma_mul_sqrt_eq (by omega) m]
  -- `(√(b² - 1) / (6b)) √m ≥ √m / 8`
  exact sqrt_sq_sub_one_div_ge hb m

/-- The first inequality of the last display, `E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m/3)` with
`σ² = (b² - 1) / (12 b²)`, for nonempty sets `B_1, …, B_b` of heights and any set `S` of `m`
points of `I` whose heights lie above all of `B_1` and at or below all of `B_b`. Fact 2.2
(`symmetric_sum_abs`) is applied to the jumps of the points of `S`.
`expected_offset_ge_sigma` is the case of the blocks of an interval and the points of
`R^in`. -/
theorem expected_offset_core_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (B : Fin b → Set ℝ) (hne : ∀ ℓ, (B ℓ).Nonempty)
    (S : Finset (Fin n))
    (hS : ∀ i ∈ S, side i = Side.inside ∧ (∀ y ∈ B ⟨0, by omega⟩, y < V i) ∧
      (∀ y ∈ B ⟨b - 1, by omega⟩, V i ≤ y)) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (childMean ε V side r) -
          mid (B ⟨0, by omega⟩) (childMean ε V side r)|) := by
  have hb0 : 0 < b := by omega
  have : Nonempty (Fin b) := ⟨⟨0, hb0⟩⟩
  -- `σ² = (b² - 1) / (12 b²)`
  have hs2 : (0 : ℝ) ≤ ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb0
    nlinarith
  have hσ2 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 =
      ((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2) := Real.sq_sqrt hs2
  have hσ4 : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 4 =
      (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hσ2]
  -- "This fixes the function `g`, and hence the number `θ`."
  have hθ : ∀ r r' : Fin n → Fin b, (∀ i, i ∉ S → r i = r' i) →
      mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) =
        mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r') -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r') := by
    intro r r' h
    rw [withoutJumps_congr b ε V side S fun i _ hi => h i hi]
  -- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
  -- children of the other points cannot reduce it": `E|θ + D| ≥ σ √(m/3)`
  have hF : Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) * Real.sqrt (S.card / 3) ≤
      finAvg (fun r : Fin n → Fin b =>
        |mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
          mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r) + jumpSum S (jump b ε) r|) :=
    symmetric_sum_abs S (jump b ε) (fun _ => Fin.revPerm)
      (fun i _ d => jump_rev b ε i d) (Real.sqrt_nonneg _)
      (fun i _ => by rw [hσ2]; exact finAvg_jump_sq hb0 ε hε i)
      (fun i _ => by rw [hσ4]; exact finAvg_jump_fourth_le hb0 ε hε i)
      (fun r => mid (B ⟨b - 1, by omega⟩) (withoutJumps b ε V side S r) -
        mid (B ⟨0, by omega⟩) (withoutJumps b ε V side S r)) hθ
  -- `mid_{B_b} ā - mid_{B_1} ā = θ + D`
  rw [finAvg_congr fun r => congrArg abs (offset_core hb ε V side B hne S hS r)]
  exact hF

/-- "So Fact 2.2 applies to `θ + D`, with `m = m_R`. Its bound holds for every `θ`, so the
children of the other points cannot reduce it. Conditionally, and hence also without the
conditioning,"

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3)`,

where `σ² = (b² - 1) / (12 b²)`: the first inequality of the last display. -/
theorem expected_offset_ge_sigma {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (((b : ℝ) ^ 2 - 1) / (12 * (b : ℝ) ^ 2)) *
        Real.sqrt ((innerPoints b V side s L).card / 3) ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  expected_offset_core_sigma hb ε hε V side (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (innerPoints b V side s L)
    (innerPoints_between_blocks hb V side s L)

/-- The last display of the proof,

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b² - 1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

"because `16 (b² - 1) ≥ 9 b²` for `b ≥ 2`." The statement is the inequality between the two
ends of this display. The first inequality of the display is `expected_offset_ge_sigma`; its
equality and its last inequality are `sigma_mul_sqrt_eq` and `sqrt_sq_sub_one_div_ge`, which
together are `sqrt_div_eight_le`. -/
theorem expected_offset_ge {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (innerPoints b V side s L).card / 8 ≤
      finAvg (fun r : Fin n → Fin b => |mid (block s L (b - 1)) (childMean ε V side r) -
        mid (block s L 0) (childMean ε V side r)|) :=
  (sqrt_div_eight_le hb (innerPoints b V side s L).card).trans
    (expected_offset_ge_sigma hb ε hε V side s hL)

/-! ### Lemma 2.3 -/

/-- **Lemma 2.3 (local gain).** In the local experiment,

`E Σ_{k=1}^{b} osc_J a_k ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} a + (1/4) √(m_R)`,

for every integer `b ≥ 2` (the manuscript has `b ≥ 3`), all colors, all heights (ties
allowed), and all positions relative to `I`. The proof is the last sentence of the
manuscript's proof: it combines display (8) (`display_8`: Steps 1–3, with Lemma 2.1) and the
last display (`expected_offset_ge`: Step 4, with Fact 2.2). -/
theorem local_gain {b : ℕ} (hb : 2 ≤ b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (V : Fin n → ℝ) (side : Fin n → Side) (s : ℝ) {L : ℝ} (hL : 0 < L) :
    ∑ ℓ : Fin b, osc (block s L ℓ) (endpointAvg ε V side) +
        (1 / 4) * Real.sqrt (innerPoints b V side s L).card ≤
      finAvg (fun r : Fin n → Fin b =>
        ∑ k : Fin b, osc (Set.Ico s (s + b * L)) (childAvg ε V side r k)) := by
  have h8 := display_8 hb ε V side s hL
  have h4 := expected_offset_ge hb ε hε V side s hL
  -- "Together with (8), this proves the inequality of the lemma."
  linarith

end

end R56Audit
end

section
/-!
# Display (2): the endpoint averages of `LocalGain.lean` are the manuscript's

Auditor's supplement (not part of the audited archive).

The manuscript defines the endpoint average of a horizontal interval `I = [I⁻, I⁺]` from the
signed counting function, `a(y) = (F(I⁻, y) + F(I⁺, y)) / 2`, and then observes that it is
`Σ_i χ_i w_i 1{V_i ≤ y}` (display (2)). `LocalGain.lean` takes the second expression as the
definition of `endpointAvg` and `childAvg`. This file proves the first equality, for `F` of
`Notation.lean`, so that Lemma 2.3 is a statement about the manuscript's objects:

* `endpointAvg_eq_F`: `(F(I⁻, y) + F(I⁺, y)) / 2 = endpointAvg … y`, when the position of a
  point relative to `I` is read from its horizontal coordinate (`sideOf`);
* `childAvg_eq_F`: the same for the child `C_{k+1} = [I⁻ + k|I|/b, I⁻ + (k+1)|I|/b]`, when
  `r i` is the index of the child that contains the point `i` of `I`;
* `exists_childIndex`: every point of `I` lies in such a child.

The identities are exact for all points with nonnegative coordinates. A point on a common
endpoint of two intervals is assigned to the left one (`sideOf`, `exists_childIndex`); the
manuscript ignores such points, which almost surely do not occur.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

/-- The colors `χ ∈ {±1}ⁿ` as real numbers. -/
def sgn (χ : Fin n → ℤˣ) : Fin n → ℝ := fun i => (((χ i : ℤˣ) : ℤ) : ℝ)

lemma abs_sgn (χ : Fin n → ℤˣ) (i : Fin n) : |sgn χ i| = 1 := by
  rcases Int.units_eq_one_or (χ i) with h | h <;> simp [sgn, h]

/-- The position of a point with horizontal coordinate `u` relative to `I = [xm, xp]`: to the
left of `I` if `u ≤ xm`, in `I` if `xm < u ≤ xp`, to the right of `I` if `xp < u`. -/
def sideOf (xm xp u : ℝ) : Side :=
  if u ≤ xm then Side.left else if u ≤ xp then Side.inside else Side.right

lemma sideOf_eq_inside_iff {xm xp u : ℝ} :
    sideOf xm xp u = Side.inside ↔ xm < u ∧ u ≤ xp := by
  unfold sideOf
  split_ifs with h1 h2
  · simp [not_lt.mpr h1]
  · simp [not_le.mp h1, h2]
  · simp [h2]

/-- `F_χ(x, y) = Σ_i χ_i 1{U_i ≤ x} 1{V_i ≤ y}` for points with nonnegative coordinates. -/
lemma F_eq_sum_ite (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) (x y : ℝ) :
    F χ P x y = ∑ i, if (P i).2 ≤ y then (if (P i).1 ≤ x then sgn χ i else 0) else 0 := by
  classical
  rw [F_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := (hP i).1
  have h2 := (hP i).2
  by_cases hy : (P i).2 ≤ y
  · by_cases hx : (P i).1 ≤ x
    · simp [hy, hx, h1, h2, sgn]
    · simp [hy, hx]
  · simp [hy]

/-- **Display (2)**, first equality: the endpoint average of `I = [xm, xp]`,
`a(y) = (F(I⁻, y) + F(I⁺, y)) / 2`, counts a point with weight `1`, `1/2` or `0` according to
its position relative to `I`. -/
theorem endpointAvg_eq_F (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) {xm xp : ℝ} (hx : xm ≤ xp) (y : ℝ) :
    (F χ P xm y + F χ P xp y) / 2 =
      endpointAvg (sgn χ) (fun i => (P i).2) (fun i => sideOf xm xp (P i).1) y := by
  rw [F_eq_sum_ite χ P hP, F_eq_sum_ite χ P hP, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold endpointAvg stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hy : (P i).2 ≤ y
  · simp only [hy, ite_true]
    unfold sideOf
    by_cases h1 : (P i).1 ≤ xm
    · have h2 : (P i).1 ≤ xp := h1.trans hx
      simp [h1, h2, oldWeight]
    · by_cases h2 : (P i).1 ≤ xp
      · simp [h1, h2, oldWeight]
        ring
      · simp [h1, h2, oldWeight]
  · simp [hy]

end

end R56Audit
end

section
/-!
# Oscillations of step functions on vertical intervals

Auditor's supplement (not part of the audited archive).

Section 2.1 of the manuscript: "All functions of the height that we consider are finite linear
combinations of the functions `y ↦ 1{V_i ≤ y}`, up to an additive constant. They take finitely
many values, so these extrema exist". This file collects what the later sections use about
such functions (`stepFn V c`) on a vertical interval `B = [s, t)`:

* `osc_le_osc_add_add`: "Applying it to `f = (f+g) + (-g)` and using `osc_B (-g) = osc_B g`
  gives `osc_B f ≤ osc_B (f+g) + osc_B g`", where "it" is the triangle inequality
  (`osc_add_le` and `osc_neg` in `Osc.lean`);
* `abs_osc_add_sub_le`: "Together with the triangle inequality itself, this is the reverse
  triangle inequality `|osc_B (f+g) - osc_B f| ≤ osc_B g`";
* `osc_stepFn_le`: `osc_B (Σ_i c_i 1{V_i ≤ ·}) ≤ Σ_i |c_i|`;
* `stepFn_single_eq_of_notMem`, `osc_stepFn_single_le`: a single jump at a height outside `B`
  is constant on `B`, and a single jump at a height in `B` has oscillation at most its size
  (Step 1 of the proof of Lemma 2.6);
* `maxOn_Ico_stepFn`, `minOn_Ico_stepFn`: the extrema over `B` are the extrema over the
  `n + 1` heights `s` and `V_i ∈ B`;
* `measurable_osc_Ico_stepFn`: `osc_B (stepFn V c)` is a measurable function of the heights.
-/

namespace R56Audit

open Finset

noncomputable section

variable {n : ℕ}

/-! ### The oscillation -/

lemma image_add_finite {α : Type*} {B : Set α} {f g : α → ℝ} (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : ((fun y => f y + g y) '' B).Finite := by
  refine (hf.image2 (fun a b => a + b) hg).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  exact Set.mem_image2.mpr ⟨f y, ⟨y, hy, rfl⟩, g y, ⟨y, hy, rfl⟩, rfl⟩

/-- If `g` takes finitely many values on `B`, then so does `-g`. -/
lemma image_neg_finite {α : Type*} {B : Set α} {g : α → ℝ} (hg : (g '' B).Finite) :
    ((fun y => -g y) '' B).Finite := by
  have h : (fun y => -g y) '' B = (fun t => -t) '' (g '' B) := by
    rw [Set.image_image]
  rw [h]
  exact hg.image _

/-- "Applying it to `f = (f+g) + (-g)` and using `osc_B (-g) = osc_B g` gives
`osc_B f ≤ osc_B (f+g) + osc_B g`." Here "it" is the triangle inequality `osc_add_le`. -/
lemma osc_le_osc_add_add {α : Type*} {B : Set α} {f g : α → ℝ} (hB : B.Nonempty)
    (hf : (f '' B).Finite) (hg : (g '' B).Finite) :
    osc B f ≤ osc B (fun y => f y + g y) + osc B g :=
  -- write `f = (f + g) + (-g)`, apply the triangle inequality to `f + g` and `-g`, and use
  -- `osc_B (-g) = osc_B g`
  calc osc B f = osc B (fun y => (f y + g y) + -g y) := osc_congr fun y _ => by ring
    _ ≤ osc B (fun y => f y + g y) + osc B (fun y => -g y) :=
        osc_add_le hB (image_add_finite hf hg) (image_neg_finite hg)
    _ = osc B (fun y => f y + g y) + osc B g := by rw [osc_neg]

/-- "Together with the triangle inequality itself, this is the reverse triangle inequality
`|osc_B (f+g) - osc_B f| ≤ osc_B g`", where "this" is `osc_B f ≤ osc_B (f+g) + osc_B g`
(`osc_le_osc_add_add`). -/
lemma abs_osc_add_sub_le {α : Type*} {B : Set α} {f g : α → ℝ} (hB : B.Nonempty)
    (hf : (f '' B).Finite) (hg : (g '' B).Finite) :
    |osc B (fun y => f y + g y) - osc B f| ≤ osc B g := by
  -- the triangle inequality itself
  have h1 : osc B (fun y => f y + g y) ≤ osc B f + osc B g := osc_add_le hB hf hg
  -- the triangle inequality applied to `f = (f + g) + (-g)`
  have h2 : osc B f ≤ osc B (fun y => f y + g y) + osc B g := osc_le_osc_add_add hB hf hg
  rw [abs_le]
  constructor <;> linarith

/-- A step function with coefficients `c` has oscillation at most `Σ_i |c_i|` on every
nonempty set of heights. -/
lemma osc_stepFn_le (V c : Fin n → ℝ) {B : Set ℝ} (hB : B.Nonempty) :
    osc B (stepFn V c) ≤ ∑ i, |c i| := by
  apply osc_le hB
  intro y _ y' _
  unfold stepFn
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := le_abs_self (c i)
  have h2 := neg_abs_le (c i)
  have h3 := abs_nonneg (c i)
  split_ifs <;> linarith

lemma osc_stepFn_nonneg (V c : Fin n → ℝ) {B : Set ℝ} (hB : B.Nonempty) :
    0 ≤ osc B (stepFn V c) :=
  osc_nonneg hB (stepFn_image_finite V c B)

/-- A step function depends on the height `y` only through the set of points of height at
most `y`. -/
lemma stepFn_congr_height (V c : Fin n → ℝ) {y y' : ℝ} (h : ∀ i, V i ≤ y ↔ V i ≤ y') :
    stepFn V c y = stepFn V c y' := by
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : V i ≤ y
  · rw [ite_eq_left hi, ite_eq_left ((h i).mp hi)]
  · rw [ite_eq_right hi, ite_eq_right (fun h' => hi ((h i).mpr h'))]

/-- A step function with one jump, at the height of the point `i`. -/
lemma stepFn_single (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) (y : ℝ) :
    stepFn V d y = if V i ≤ y then d i else 0 := by
  unfold stepFn
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rw [hd k hk]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **One jump outside `B`** (Step 1 of the proof of Lemma 2.6). "If `V_i ∉ B`, the added
function is constant on `B`": a step function with its only jump at the height `V_i`, of size
`d_i`, is constant on a vertical interval `B = [s, t)` that does not contain `V_i`. Its value
on `B` is `d_i` if `V_i` lies below `B`, and `0` if `V_i` lies above `B`. -/
lemma stepFn_single_eq_of_notMem (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0)
    {s t : ℝ} (hi : V i ∉ Set.Ico s t) {y : ℝ} (hy : y ∈ Set.Ico s t) :
    stepFn V d y = if V i < s then d i else 0 := by
  rw [stepFn_single V d i hd]
  by_cases hlo : V i < s
  · -- `V_i` lies below `B`, so the jump is counted at every height of `B`
    rw [ite_eq_left hlo, ite_eq_left (hlo.le.trans hy.1)]
  · -- `V_i` lies above `B`, so the jump is counted at no height of `B`
    have hhi : t ≤ V i := by
      by_contra hlt
      exact hi ⟨not_lt.mp hlo, not_le.mp hlt⟩
    rw [ite_eq_right hlo, ite_eq_right (not_le.mpr (hy.2.trans_le hhi))]

/-- **One jump** (Step 1 of the proof of Lemma 2.6). Let the step function have its only jump
at the height `V_i`, of size `d_i`. "If `V_i ∉ B`, the added function is constant on `B`
\[…\]. If `V_i ∈ B`, the added function has oscillation at most `1` on `B`" (here: at most
`|d_i|`). -/
lemma osc_stepFn_single_le (V d : Fin n → ℝ) (i : Fin n) (hd : ∀ k, k ≠ i → d k = 0) {s t : ℝ}
    (hst : s < t) :
    osc (Set.Ico s t) (stepFn V d) ≤ if V i ∈ Set.Ico s t then |d i| else 0 := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply osc_le hB
  intro y hy y' hy'
  by_cases hi : V i ∈ Set.Ico s t
  · -- `V_i ∈ B`: two values of a function that takes only the values `d_i` and `0`
    rw [stepFn_single V d i hd, stepFn_single V d i hd, ite_eq_left hi]
    have h1 := le_abs_self (d i)
    have h2 := neg_abs_le (d i)
    have h3 := abs_nonneg (d i)
    split_ifs <;> linarith
  · -- `V_i ∉ B`: the function is constant on `B`
    rw [stepFn_single_eq_of_notMem V d i hd hi hy, stepFn_single_eq_of_notMem V d i hd hi hy',
      sub_self, ite_eq_right hi]

/-! ### The extrema over an interval are extrema over finitely many heights -/

/-- The candidate heights in `B = [s, t)`: the bottom `s`, and the heights of the points in
`B`. -/
def candY (s t : ℝ) (o : Option (Fin n)) (V : Fin n → ℝ) : ℝ :=
  o.elim s (fun i => if s ≤ V i ∧ V i < t then V i else s)

lemma candY_mem {s t : ℝ} (hst : s < t) (o : Option (Fin n)) (V : Fin n → ℝ) :
    candY s t o V ∈ Set.Ico s t := by
  cases o with
  | none => exact ⟨le_rfl, hst⟩
  | some i =>
    simp only [candY, Option.elim_some]
    split_ifs with h
    · exact h
    · exact ⟨le_rfl, hst⟩

lemma measurable_candY (s t : ℝ) (o : Option (Fin n)) : Measurable (candY (n := n) s t o) := by
  cases o with
  | none => exact measurable_const
  | some i =>
    change Measurable (fun V : Fin n → ℝ => if s ≤ V i ∧ V i < t then V i else s)
    refine Measurable.ite ?_ (measurable_pi_apply i) measurable_const
    exact (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

/-- Every value of a step function on `[s, t)` is its value at a candidate height. -/
lemma exists_candY (V c : Fin n → ℝ) {s t y : ℝ} (hy : y ∈ Set.Ico s t) :
    ∃ o : Option (Fin n), stepFn V c (candY s t o V) = stepFn V c y := by
  classical
  by_cases hT : ∃ i, s ≤ V i ∧ V i ≤ y
  · have hne : (Finset.univ.filter (fun i => s ≤ V i ∧ V i ≤ y)).Nonempty := by
      obtain ⟨i, hi⟩ := hT
      exact ⟨i, by simp [hi]⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ V hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmax
    refine ⟨some i, stepFn_congr_height V c fun k => ?_⟩
    have hc : candY s t (some i) V = V i := by
      simp only [candY, Option.elim_some]
      rw [ite_eq_left ⟨hi.1, hi.2.trans_lt hy.2⟩]
    rw [hc]
    constructor
    · intro hk
      exact hk.trans hi.2
    · intro hk
      by_cases hs : s ≤ V k
      · exact hmax k ⟨hs, hk⟩
      · exact (not_le.mp hs).le.trans hi.1
  · refine ⟨none, stepFn_congr_height V c fun k => ?_⟩
    simp only [candY, Option.elim_none]
    constructor
    · intro hk
      exact hk.trans hy.1
    · intro hk
      by_contra hs
      exact hT ⟨k, (not_le.mp hs).le, hk⟩

/-- `max_B` of a step function over `B = [s, t)` is the maximum over the candidate heights. -/
theorem maxOn_Ico_stepFn (V c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    maxOn (Set.Ico s t) (stepFn V c) = ⨆ o : Option (Fin n), stepFn V c (candY s t o V) := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply le_antisymm
  · apply maxOn_le hB
    intro y hy
    obtain ⟨o, ho⟩ := exists_candY V c hy
    rw [← ho]
    exact le_ciSup (f := fun o : Option (Fin n) => stepFn V c (candY s t o V))
      (Set.finite_range _).bddAbove o
  · exact ciSup_le fun o => le_maxOn (stepFn_image_finite V c _) (candY_mem hst o V)

/-- `min_B` of a step function over `B = [s, t)` is the minimum over the candidate heights. -/
theorem minOn_Ico_stepFn (V c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    minOn (Set.Ico s t) (stepFn V c) = ⨅ o : Option (Fin n), stepFn V c (candY s t o V) := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  apply le_antisymm
  · exact le_ciInf fun o => minOn_le (stepFn_image_finite V c _) (candY_mem hst o V)
  · apply le_minOn hB
    intro y hy
    obtain ⟨o, ho⟩ := exists_candY V c hy
    rw [← ho]
    exact ciInf_le (f := fun o : Option (Fin n) => stepFn V c (candY s t o V))
      (Set.finite_range _).bddBelow o

lemma measurable_stepFn_candY (c : Fin n → ℝ) (s t : ℝ) (o : Option (Fin n)) :
    Measurable (fun V : Fin n → ℝ => stepFn V c (candY s t o V)) := by
  unfold stepFn
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_candY s t o))
    measurable_const measurable_const

/-- The oscillation of a step function on a vertical interval is a measurable function of the
heights. -/
theorem measurable_osc_Ico_stepFn (c : Fin n → ℝ) {s t : ℝ} (hst : s < t) :
    Measurable (fun V : Fin n → ℝ => osc (Set.Ico s t) (stepFn V c)) := by
  have h : (fun V : Fin n → ℝ => osc (Set.Ico s t) (stepFn V c)) =
      fun V => (⨆ o : Option (Fin n), stepFn V c (candY s t o V)) -
        ⨅ o : Option (Fin n), stepFn V c (candY s t o V) := by
    funext V
    unfold osc
    rw [maxOn_Ico_stepFn V c hst, minOn_Ico_stepFn V c hst]
  rw [h]
  exact (Measurable.iSup fun o => measurable_stepFn_candY c s t o).sub
    (Measurable.iInf fun o => measurable_stepFn_candY c s t o)

end

end R56Audit
end

section
/-!
# The potential `Z_j` of the manuscript (display (1)), with heights in the continuum

Auditor's supplement (not part of the audited archive).

Section 2.4: fix `h ≥ 1` and `M = b^{h-1}`. "At stage `j`, `0 ≤ j ≤ h`, cut `[0,1]`
horizontally into `b^j` intervals of length `b^{-j}`, and vertically into `b^{h-j}` intervals
of length `b^{j-h}`. Their products are the cells of stage `j`. \[…\] the potential is

`Z_j = (1 / (bM)) Σ_{stage-j cells I × B} osc_B a^{(I)}`",

where `a^{(I)}(y) = (F(I⁻, y) + F(I⁺, y)) / 2` is the endpoint average of `I = [I⁻, I⁺]`, the
vertical intervals are closed at the bottom and open at the top, and `osc_B` is the
oscillation over all heights `y ∈ B`.

| Manuscript | Here |
| --- | --- |
| length `b^{j-h}` of a vertical interval of stage `j` | `vlen b h j` |
| the `v`-th vertical interval `[v b^{j-h}, (v+1) b^{j-h})` of stage `j` | `vcell b h j v` |
| the `c`-th horizontal interval `[c b^{-j}, (c+1) b^{-j}]` of stage `j` | its endpoints |
| endpoint average `a^{(I)}`, display (2) | `endAvg χ P I⁻ I⁺` |
| the potential `Z_j`, display (1) | `Zpot χ b h j P` |

`Zpot` is the definition of the manuscript, word for word, for the function `F_χ` of
`Notation.lean`. Its extrema are over the continuum of heights of each cell; nothing is
sampled.

For the proofs it is convenient to read the potential from the heights and from the index of
the stage-`j` horizontal interval that contains each point (`Zstep`): for points with
nonnegative coordinates the two agree (`Zpot_eq_Zstep`). The index is
`Riesz.gridIndex (b^j) u = ⌈b^j u⌉ - 1`, the number `c` with `c b^{-j} < u ≤ (c+1) b^{-j}`;
this matches `F_χ`, which counts the points of the closed rectangle `[0,x] × [0,y]`.

* `Zpot_nonneg`, `Zpot_le_two_supNorm`: **display (9)**, `0 ≤ Z_j ≤ 2 ‖F‖∞`;
* `measurable_Zstep_uncurry`: the potential is a measurable function of the heights and the
  indices;
* `gridIndex_succ`: the index at stage `j+1` is `b` times the index at stage `j` plus the
  next digit.
-/

namespace R56Audit

open Finset MeasureTheory Riesz Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Stage geometry -/

/-- `b^{j-h}`, the length of the vertical intervals of stage `j`. -/
def vlen (b h j : ℕ) : ℝ := (b : ℝ) ^ j / (b : ℝ) ^ h

lemma vlen_pos {b : ℕ} (hb : 0 < b) (h j : ℕ) : 0 < vlen b h j := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold vlen
  positivity

lemma vlen_succ (b h j : ℕ) : vlen b h (j + 1) = b * vlen b h j := by
  unfold vlen
  rw [pow_succ]
  ring

/-- The `v`-th vertical interval of stage `j`: `[v b^{j-h}, (v+1) b^{j-h})`, closed at the
bottom and open at the top. -/
def vcell (b h j v : ℕ) : Set ℝ := Set.Ico (v * vlen b h j) ((v + 1) * vlen b h j)

lemma vcell_lt {b : ℕ} (hb : 0 < b) (h j v : ℕ) :
    (v : ℝ) * vlen b h j < ((v : ℝ) + 1) * vlen b h j := by
  have := vlen_pos hb h j
  nlinarith

lemma vcell_nonempty {b : ℕ} (hb : 0 < b) (h j v : ℕ) : (vcell b h j v).Nonempty :=
  ⟨v * vlen b h j, le_rfl, vcell_lt hb h j v⟩

/-- The vertical intervals of stage `j ≤ h` lie in `[0, 1)`. -/
lemma vcell_subset_unit {b h j v : ℕ} (hb : 0 < b) (hj : j ≤ h) (hv : v < b ^ (h - j)) :
    vcell b h j v ⊆ Set.Ico (0 : ℝ) 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hL := vlen_pos hb h j
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hv1 : (v : ℝ) + 1 ≤ (b : ℝ) ^ (h - j) := by exact_mod_cast hv
  have hfull : (b : ℝ) ^ (h - j) * vlen b h j = 1 := by
    unfold vlen
    rw [← mul_div_assoc, ← pow_add, Nat.sub_add_cancel hj]
    exact div_self (by positivity)
  rintro y ⟨h1, h2⟩
  constructor
  · exact (mul_nonneg hv0 hL.le).trans h1
  · calc y < ((v : ℝ) + 1) * vlen b h j := h2
      _ ≤ (b : ℝ) ^ (h - j) * vlen b h j := mul_le_mul_of_nonneg_right hv1 hL.le
      _ = 1 := hfull

/-- The vertical interval `b v + ℓ` of stage `j` is the block `B_{ℓ+1}` of the `v`-th vertical
interval of stage `j + 1`. -/
lemma vcell_eq_block (b h j v ℓ : ℕ) :
    vcell b h j (b * v + ℓ) = block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ := by
  unfold vcell block
  rw [vlen_succ]
  push_cast
  congr 1 <;> ring

/-- The `v`-th vertical interval of stage `j + 1`, as the interval `J` of Lemma 2.3. -/
lemma vcell_succ_eq (b h j v : ℕ) :
    vcell b h (j + 1) v =
      Set.Ico ((v : ℝ) * vlen b h (j + 1)) ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j) := by
  unfold vcell
  rw [vlen_succ]
  congr 1
  ring

/-! ### The potential, as in the manuscript -/

/-- The endpoint average `a^{(I)}(y) = (F(I⁻, y) + F(I⁺, y)) / 2` of the horizontal interval
`I = [xm, xp]`, display (2). -/
def endAvg (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp : ℝ) : ℝ → ℝ :=
  fun y => (F χ P xm y + F χ P xp y) / 2

/-- **The potential, display (1)**:
`Z_j = (1 / b^h) Σ_{stage-j cells I × B} osc_B a^{(I)}`, the sum over the `b^j` horizontal
intervals `I = [c b^{-j}, (c+1) b^{-j}]` and the `b^{h-j}` vertical intervals
`B = [v b^{j-h}, (v+1) b^{j-h})` of stage `j`. (`b^h = bM`.) -/
def Zpot (χ : Fin n → ℤˣ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
    osc (vcell b h j v)
      (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))) /
    (b : ℝ) ^ h

/-! ### The potential, read from the heights and the cell indices -/

/-- The position, relative to the `c`-th horizontal interval of a stage, of a point whose
horizontal coordinate lies in the interval with index `g` of that stage. -/
def sideIdx (g : ℤ) (c : ℕ) : Side :=
  if g < c then Side.left else if g = c then Side.inside else Side.right

/-- The potential of stage `j` for colors `ε`, heights `V` and stage-`j` indices `g`. -/
def Zstep (ε : Fin n → ℝ) (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
    osc (vcell b h j v) (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h

/-- `u ≤ z / N` exactly when the index of the cell `(k/N, (k+1)/N]` containing `u` is less
than `z`. -/
lemma le_div_iff_gridIndex_lt {N : ℕ} (hN : 0 < N) (u : ℝ) (z : ℤ) :
    u ≤ (z : ℝ) / N ↔ gridIndex N u < z := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridIndex
  rw [le_div_iff₀ hNR, mul_comm u, ← Int.ceil_le]
  omega

/-- The position of a point relative to the `c`-th horizontal interval of stage `j` is
determined by its stage-`j` index. -/
lemma sideOf_grid {b : ℕ} (hb : 0 < b) (j c : ℕ) (u : ℝ) :
    sideOf (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j) u =
      sideIdx (gridIndex (b ^ j) u) c := by
  have hN : 0 < b ^ j := pow_pos hb j
  have h1 : u ≤ ((c : ℕ) : ℝ) / (b : ℝ) ^ j ↔ gridIndex (b ^ j) u < (c : ℤ) := by
    have := le_div_iff_gridIndex_lt hN u (c : ℤ)
    push_cast at this
    exact this
  have h2 : u ≤ (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j ↔ gridIndex (b ^ j) u < (c : ℤ) + 1 := by
    have := le_div_iff_gridIndex_lt hN u ((c : ℤ) + 1)
    push_cast at this
    exact this
  unfold sideOf sideIdx
  by_cases a1 : gridIndex (b ^ j) u < (c : ℤ)
  · rw [ite_eq_left (h1.mpr a1), ite_eq_left a1]
  · rw [ite_eq_right (fun h => a1 (h1.mp h)), ite_eq_right a1]
    by_cases a2 : gridIndex (b ^ j) u = (c : ℤ)
    · rw [ite_eq_left (h2.mpr (by omega)), ite_eq_left a2]
    · rw [ite_eq_right (fun h => a2 (by have := h2.mp h; omega)), ite_eq_right a2]

/-- For points with nonnegative coordinates, the potential of the manuscript is the potential
read from the heights and the stage-`j` indices. -/
theorem Zpot_eq_Zstep {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ)
    (hP : ∀ i, 0 ≤ (P i).1 ∧ 0 ≤ (P i).2) :
    Zpot χ b h j P =
      Zstep (sgn χ) b h j (fun i => (P i).2) (fun i => gridIndex (b ^ j) (P i).1) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zpot Zstep
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun v _ => ?_
  congr 1
  funext y
  have hx : ((c : ℕ) : ℝ) / (b : ℝ) ^ j ≤ (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  change (F χ P _ y + F χ P _ y) / 2 = _
  rw [endpointAvg_eq_F χ P hP hx y]
  congr 1
  funext i
  exact sideOf_grid hb j c (P i).1

/-! ### Bounds: display (9) -/

lemma abs_oldWeight_le (sd : Side) : |oldWeight sd| ≤ 1 := by
  cases sd with
  | left => simp [oldWeight]
  | inside => rw [oldWeight, abs_of_pos (by norm_num)]; norm_num
  | right => simp [oldWeight]

lemma osc_endpointAvg_le_card (ε V : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (side : Fin n → Side)
    {B : Set ℝ} (hB : B.Nonempty) : osc B (endpointAvg ε V side) ≤ n := by
  refine (osc_stepFn_le V _ hB).trans ?_
  calc ∑ i, |ε i * oldWeight (side i)| ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        calc |ε i| * |oldWeight (side i)| ≤ 1 * 1 :=
              mul_le_mul (hε i) (abs_oldWeight_le _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = n := by simp

lemma Zstep_nonneg {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (V : Fin n → ℝ)
    (g : Fin n → ℤ) : 0 ≤ Zstep ε b h j V g := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zstep
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun v _ =>
    osc_stepFn_nonneg V _ (vcell_nonempty hb h j v)

lemma card_cells {b h j : ℕ} (hj : j ≤ h) : (b : ℝ) ^ j * (b : ℝ) ^ (h - j) = (b : ℝ) ^ h := by
  rw [← pow_add, Nat.add_sub_cancel' hj]

/-- For `j ≤ h` the potential is at most `n`. -/
lemma Zstep_le {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (V : Fin n → ℝ) (g : Fin n → ℤ) : Zstep ε b h j V g ≤ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zstep
  rw [div_le_iff₀ (by positivity)]
  calc ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v) (endpointAvg ε V (fun i => sideIdx (g i) c))
      ≤ ∑ _c : Fin (b ^ j), ∑ _v : Fin (b ^ (h - j)), (n : ℝ) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ =>
          osc_endpointAvg_le_card ε V hε _ (vcell_nonempty hb h j v)
    _ = n * (b : ℝ) ^ h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← card_cells hj]
        ring

lemma abs_Zstep_le {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (V : Fin n → ℝ) (g : Fin n → ℤ) : |Zstep ε b h j V g| ≤ n := by
  rw [abs_of_nonneg (Zstep_nonneg hb ε h j V g)]
  exact Zstep_le hb hj ε hε V g

/-- `F_χ(x, ·)` is a step function of the height, for all positions of the points. -/
lemma F_eq_stepFn (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (x y : ℝ) :
    F χ P x y = stepFn (fun i => (P i).2)
      (fun i => if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 then sgn χ i else 0) y := by
  classical
  rw [F_eq_filter, Finset.sum_filter]
  unfold stepFn
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  by_cases hy : (P i).2 ≤ y
  · by_cases hc : 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2
    · rw [ite_eq_left hy, ite_eq_left hc, ite_eq_left ⟨hc.1, hc.2.1, hc.2.2, hy⟩]
      rfl
    · rw [ite_eq_left hy, ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]
  · rw [ite_eq_right hy, ite_eq_right (fun h => hy h.2.2.2)]

/-- The endpoint average takes finitely many values. -/
lemma endAvg_image_finite (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ) (xm xp : ℝ) (B : Set ℝ) :
    ((endAvg χ P xm xp) '' B).Finite := by
  have h : endAvg χ P xm xp = stepFn (fun i => (P i).2)
      (fun i => ((if 0 ≤ (P i).1 ∧ (P i).1 ≤ xm ∧ 0 ≤ (P i).2 then sgn χ i else 0) +
        (if 0 ≤ (P i).1 ∧ (P i).1 ≤ xp ∧ 0 ≤ (P i).2 then sgn χ i else 0)) / 2) := by
    funext y
    unfold endAvg
    rw [F_eq_stepFn, F_eq_stepFn, stepFn_div, stepFn_add]
  rw [h]
  exact stepFn_image_finite _ _ B

/-- **Display (9), lower bound**: `0 ≤ Z_j`. -/
theorem Zpot_nonneg {b : ℕ} (hb : 0 < b) (χ : Fin n → ℤˣ) (h j : ℕ) (P : Fin n → ℝ × ℝ) :
    0 ≤ Zpot χ b h j P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Zpot
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun v _ =>
    osc_nonneg (vcell_nonempty hb h j v) (endAvg_image_finite χ P _ _ _)

/-- **Display (9), upper bound**: `Z_j ≤ 2 ‖F‖∞` for `0 ≤ j ≤ h`. "By (3), an oscillation
`osc_B a^{(I)}` is a difference of two values of `a^{(I)}`, and each of them is an average of
two values of `F`." -/
theorem Zpot_le_two_supNorm {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ)
    (P : Fin n → ℝ × ℝ) : Zpot χ b h j P ≤ 2 * supNorm χ P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpow : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  unfold Zpot
  rw [div_le_iff₀ (by positivity)]
  have hcell : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j))),
      osc (vcell b h j v)
        (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j)) ≤
        2 * supNorm χ P := by
    intro c v
    have hc0 : (0 : ℝ) ≤ (c : ℕ) := Nat.cast_nonneg _
    have hc1 : ((c : ℕ) : ℝ) + 1 ≤ (b : ℝ) ^ j := by exact_mod_cast c.isLt
    have hxm : ((c : ℕ) : ℝ) / (b : ℝ) ^ j ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hpow).mpr (by linarith)⟩
    have hxp : (((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hpow).mpr hc1⟩
    apply osc_le (vcell_nonempty hb h j v)
    intro y hy y' hy'
    have hyu := vcell_subset_unit hb hj v.isLt hy
    have hyu' := vcell_subset_unit hb hj v.isLt hy'
    have hY : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hyu.1, hyu.2.le⟩
    have hY' : y' ∈ Set.Icc (0 : ℝ) 1 := ⟨hyu'.1, hyu'.2.le⟩
    have a1 := abs_le.mp (le_supNorm χ P hxm hY)
    have a2 := abs_le.mp (le_supNorm χ P hxp hY)
    have a3 := abs_le.mp (le_supNorm χ P hxm hY')
    have a4 := abs_le.mp (le_supNorm χ P hxp hY')
    unfold endAvg
    linarith [a1.2, a2.2, a3.1, a4.1]
  calc ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
        osc (vcell b h j v)
          (endAvg χ P (((c : ℕ) : ℝ) / (b : ℝ) ^ j) ((((c : ℕ) : ℝ) + 1) / (b : ℝ) ^ j))
      ≤ ∑ _c : Fin (b ^ j), ∑ _v : Fin (b ^ (h - j)), 2 * supNorm χ P :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ => hcell c v
    _ = 2 * supNorm χ P * (b : ℝ) ^ h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← card_cells hj]
        ring

/-! ### Measurability -/

/-- The potential is a measurable function of the heights. -/
lemma measurable_Zstep {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (g : Fin n → ℤ) :
    Measurable (fun V : Fin n → ℝ => Zstep ε b h j V g) := by
  unfold Zstep
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun v _ => ?_
  exact measurable_osc_Ico_stepFn _ (vcell_lt hb h j v)

/-- The potential is a measurable function of the heights and the indices. -/
theorem measurable_Zstep_uncurry {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℤ) => Zstep ε b h j p.1 p.2) :=
  measurable_from_prod_countable_left fun g => measurable_Zstep hb ε h j g

/-! ### The next digit -/

/-- The stage-`(j+1)` indices of points with stage-`j` indices `g` and next digits `r`. -/
def refineIdx {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) : Fin n → ℤ :=
  fun i => (b : ℤ) * g i + ((r i : ℕ) : ℤ)

/-- The index at stage `j + 1` is `b` times the index at stage `j` plus the next digit. -/
lemma gridIndex_succ {b : ℕ} (hb : 0 < b) (j : ℕ) (u : ℝ) :
    gridIndex (b ^ (j + 1)) u =
      (b : ℤ) * gridIndex (b ^ j) u + ((freshGridIndex (b ^ j) b hb u : ℕ) : ℤ) := by
  have h1 := freshGridIndex_eq_emod (b ^ j) b (pow_pos hb j) hb u
  have h2 := gridIndex_mul_ediv (b ^ j) b hb u
  have h3 := Int.mul_ediv_add_emod (gridIndex (b ^ j * b) u) (b : ℤ)
  rw [pow_succ, h1, ← h2]
  exact h3.symm

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.Bridge

open TusnadyPlane.RandomPoints

theorem sampleLaw_eq (n : ℕ) : sampleLaw n = Riesz.PointSets.unifPts n := by
  unfold sampleLaw squareLaw Riesz.PointSets.unifPts
  simp_rw [← Riesz.PointSets.unitSq_eq]

/-- Boolean colouring to a ±1 colouring. -/
def chiU {n : ℕ} (χ : Coloring n) : Fin n → ℤˣ := fun i => if χ i then 1 else -1

theorem chiU_cast {n : ℕ} (χ : Coloring n) (i : Fin n) :
    (((chiU χ i : ℤˣ) : ℤ) : ℝ) = sign (χ i) := by
  unfold chiU sign
  cases χ i <;> simp

theorem signedCount_eq {n : ℕ} (P : Sample n) (χ : Coloring n) (x y : ℝ) :
    signedCount P χ x y = R56Audit.F (chiU χ) P x y := by
  classical
  unfold signedCount R56Audit.F
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y) ↔ ((P i).1 ∈ Set.Icc 0 x ∧ (P i).2 ∈ Set.Icc 0 y) := by
    simp only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero]
    tauto
  by_cases hq : P i ∈ Set.Icc (0 : ℝ × ℝ) (x, y)
  · rw [if_pos hq, if_pos (h.mp hq), chiU_cast]
  · rw [if_neg hq, if_neg (fun h' => hq (h.mpr h'))]

end TusnadyPlane.Dev.Bridge
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.Bridge

open TusnadyPlane.RandomPoints

theorem discrepancy_eq {n : ℕ} (P : Sample n) (χ : Coloring n) :
    discrepancy P χ = R56Audit.supNorm (chiU χ) P := by
  unfold discrepancy R56Audit.supNorm
  rw [iSup]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_range, Prod.exists, Subtype.exists, signedCount_eq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

theorem chiU_surj {n : ℕ} (χ' : Fin n → ℤˣ) : ∃ χ : Coloring n, chiU χ = χ' := by
  refine ⟨fun i => decide (χ' i = 1), ?_⟩
  funext i
  unfold chiU
  rcases Int.units_eq_one_or (χ' i) with h | h <;> simp [h]

end TusnadyPlane.Dev.Bridge
end

section
/-!
# The next digits are independent and uniform given the heights and the earlier digits

Auditor's supplement (not part of the audited archive).

Section 2.4: "Let `𝓕_j` be the σ-field generated by all heights and by the first `j` base-`b`
digits of every horizontal coordinate. \[…\] The `(j+1)`-st digits, which we call the next
digits at stage `j`, are independent and uniform conditional on `𝓕_j`."

`condExp_fresh_given_heights` is this statement for `n` independent uniform points of the
unit square, in the form: the conditional expectation of a bounded measurable function of
the heights, the cell indices at resolution `k` and the next digits (base `m`), given the
heights and the cell indices, is the uniform average over the next digits.

The archive has the corresponding statement for the horizontal coordinates alone
(`Riesz.condExp_freshGrid_with_past`), with the heights replaced by fixed labels.
-/

namespace R56Audit

open MeasureTheory Riesz Riesz.PointSets Oscillation

noncomputable section

/-- The heights of the points, and the indices of the cells `(c/k, (c+1)/k]` that contain
their horizontal coordinates. -/
def coarseInfo (n k : ℕ) (P : Fin n → ℝ × ℝ) : (Fin n → ℝ) × (Fin n → ℤ) :=
  (fun i => (P i).2, fun i => gridIndex k (P i).1)

lemma measurable_coarseInfo (n k : ℕ) : Measurable (coarseInfo n k) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun i => ?_) (measurable_pi_iff.mpr fun i => ?_)
  · exact measurable_snd.comp (measurable_pi_apply i)
  · exact (measurable_gridIndex k).comp (measurable_fst.comp (measurable_pi_apply i))

/-- The next digits in base `m`, after the cell indices at resolution `k`. -/
def freshInfo (n k m : ℕ) (hm : 0 < m) (P : Fin n → ℝ × ℝ) : Fin n → Fin m :=
  fun i => freshGridIndex k m hm (P i).1

lemma measurable_freshInfo (n k m : ℕ) (hm : 0 < m) : Measurable (freshInfo n k m hm) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact (measurable_freshGridIndex k m hm).comp (measurable_fst.comp (measurable_pi_apply i))

/-!
### Proof of the conditional law

For fixed heights, only the horizontal coordinates are integrated, and the archive's theorem
for the horizontal coordinates applies (`integral_fresh_eq_integral_finAvg`). Integrating
over the heights gives the statement in integrated form (`integral_fresh_given_heights`).
Applied to the function cut off outside an event of the conditioning σ-algebra, this is the
characterization of the conditional expectation.
-/

/-- The coarse information of the points `(U i, V i)`: the heights `V`, the cell indices of `U`. -/
lemma coarseInfo_pair (n k : ℕ) (U V : Fin n → ℝ) :
    coarseInfo n k (fun i => (U i, V i)) = (V, sampleGridIndex n k U) := rfl

/-- The next digits of the points `(U i, V i)` are those of the horizontal coordinates `U`. -/
lemma freshInfo_pair (n k m : ℕ) (hm : 0 < m) (U V : Fin n → ℝ) :
    freshInfo n k m hm (fun i => (U i, V i)) = sampleFreshIndex n k m hm U := rfl

/-- The uniform average over the `m ^ n` vectors of `n` digits in base `m`. -/
lemma finAvg_digits (n m : ℕ) (f : (Fin n → Fin m) → ℝ) :
    finAvg f = (∑ a, f a) / (m : ℝ) ^ n := by
  simp [finAvg]

/-- Horizontal coordinates alone: under the integral, a bounded function of the cell indices
and the next digits may be replaced by its uniform average over the next digits. -/
lemma integral_fresh_eq_integral_finAvg (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (G : (Fin n → ℤ) → (Fin n → Fin m) → ℝ) (K : ℝ) (hG : ∀ c a, |G c a| ≤ K) :
    ∫ U, G (sampleGridIndex n k U) (sampleFreshIndex n k m hm U) ∂coordinateSampleLaw n =
      ∫ U, finAvg (fun a => G (sampleGridIndex n k U) a) ∂coordinateSampleLaw n := by
  have hmeas : Measurable (fun U => G (sampleGridIndex n k U) (sampleFreshIndex n k m hm U)) :=
    (measurable_of_countable (fun z : (Fin n → ℤ) × (Fin n → Fin m) => G z.1 z.2)).comp
      ((measurable_sampleGridIndex n k).prodMk (measurable_sampleFreshIndex n k m hm))
  have hint : Integrable (fun U => G (sampleGridIndex n k U) (sampleFreshIndex n k m hm U))
      (coordinateSampleLaw n) :=
    Integrable.of_bound hmeas.aestronglyMeasurable K (Filter.Eventually.of_forall fun _ => hG _ _)
  calc ∫ U, G (sampleGridIndex n k U) (sampleFreshIndex n k m hm U) ∂coordinateSampleLaw n
      = ∫ U, ((coordinateSampleLaw n)[fun U =>
          G (sampleGridIndex n k U) (sampleFreshIndex n k m hm U) | sampleGridSigma n k]) U
          ∂coordinateSampleLaw n :=
        (integral_condExp (measurable_sampleGridIndex n k).comap_le).symm
    _ = ∫ U, (∑ a, G (sampleGridIndex n k U) a) / (m : ℝ) ^ n ∂coordinateSampleLaw n :=
        integral_congr_ae (condExp_freshGrid_with_past n k m hk hm G hint)
    _ = ∫ U, finAvg (fun a => G (sampleGridIndex n k U) a) ∂coordinateSampleLaw n := by
        simp only [finAvg_digits]

/-- A function of the coarse information and the next digits, measurable in the former, is
measurable: the next digits take finitely many values. -/
lemma measurable_coarse_fresh (n k m : ℕ) (hm : 0 < m)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r)) :
    Measurable (fun P => H (coarseInfo n k P) (freshInfo n k m hm P)) :=
  (measurable_from_prod_countable_left
      (f := fun z : ((Fin n → ℝ) × (Fin n → ℤ)) × (Fin n → Fin m) => H z.1 z.2) hH).comp
    ((measurable_coarseInfo n k).prodMk (measurable_freshInfo n k m hm))

/-- A bounded function of the coarse information and of the next digits is integrable. -/
lemma integrable_coarse_fresh (n k m : ℕ) (hm : 0 < m)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r))
    (K : ℝ) (hK : ∀ p r, |H p r| ≤ K) :
    Integrable (fun P => H (coarseInfo n k P) (freshInfo n k m hm P)) (pointSampleLaw n) :=
  Integrable.of_bound (measurable_coarse_fresh n k m hm H hH).aestronglyMeasurable K
    (Filter.Eventually.of_forall fun _ => hK _ _)

/-- The average over the next digits is a measurable function of the coarse information. -/
lemma measurable_finAvg_coarse (n m : ℕ)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r)) :
    Measurable (fun p => finAvg (fun r => H p r)) :=
  (Finset.measurable_sum _ fun r _ => hH r).div_const _

/-- The average over the next digits of a bounded function is integrable. -/
lemma integrable_finAvg_coarse (n k m : ℕ)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r))
    (K : ℝ) (hK : ∀ p r, |H p r| ≤ K) :
    Integrable (fun P => finAvg (fun r => H (coarseInfo n k P) r)) (pointSampleLaw n) :=
  (integrable_finsetSum _ fun r _ => Integrable.of_bound
    ((hH r).comp (measurable_coarseInfo n k)).aestronglyMeasurable K
    (Filter.Eventually.of_forall fun _ => hK _ r)).div_const _

/-- Integrated form: under the integral, a bounded function of the coarse information and the
next digits may be replaced by its uniform average over the next digits. -/
lemma integral_fresh_given_heights (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r))
    (K : ℝ) (hK : ∀ p r, |H p r| ≤ K) :
    ∫ P, H (coarseInfo n k P) (freshInfo n k m hm P) ∂pointSampleLaw n =
      ∫ P, finAvg (fun r => H (coarseInfo n k P) r) ∂pointSampleLaw n := by
  -- integrate the horizontal coordinates `U` first, for fixed heights `V`
  rw [integral_point_eq_vertical_horizontal _ (integrable_coarse_fresh n k m hm H hH K hK),
    integral_point_eq_vertical_horizontal _ (integrable_finAvg_coarse n k m H hH K hK)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only [coarseInfo_pair, freshInfo_pair]
  exact integral_fresh_eq_integral_finAvg n k m hk hm (fun c a => H (V, c) a) K
    fun c a => hK (V, c) a

/-- **The next digits are independent and uniform conditional on the heights and the earlier
digits.** For a bounded function `H` of the heights and cell indices `p` and of the next
digits `r`, measurable in `p`,

`E[H(p, r) | heights, cell indices] = (average of H(p, ·) over all values of the next digits)`

almost surely, for `n` independent uniform points of `[0,1]²`. -/
theorem condExp_fresh_given_heights (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (H : (Fin n → ℝ) × (Fin n → ℤ) → (Fin n → Fin m) → ℝ)
    (hH : ∀ r, Measurable (fun p => H p r))
    (K : ℝ) (hK : ∀ p r, |H p r| ≤ K) :
    (pointSampleLaw n)[fun P => H (coarseInfo n k P) (freshInfo n k m hm P) |
        MeasurableSpace.comap (coarseInfo n k) inferInstance] =ᵐ[pointSampleLaw n]
      fun P => finAvg (fun r => H (coarseInfo n k P) r) := by
  have hc : Measurable (coarseInfo n k) := measurable_coarseInfo n k
  -- uniqueness of the conditional expectation: compare the integrals over the events of the
  -- conditioning σ-algebra
  refine (ae_eq_condExp_of_forall_setIntegral_eq hc.comap_le
    (integrable_coarse_fresh n k m hm H hH K hK)
    (fun s _ _ => (integrable_finAvg_coarse n k m H hH K hK).integrableOn) ?_ ?_).symm
  · -- such an event is `coarseInfo n k P ∈ S` for a measurable set `S`
    rintro s ⟨S, hS, rfl⟩ -
    -- the integrated form, for `H` cut off outside `S`
    have hcut := integral_fresh_given_heights n k m hk hm
      (fun p r => S.indicator (fun q => H q r) p) (fun r => (hH r).indicator hS) K
      (fun p r => (norm_indicator_le_norm_self (fun q => H q r) p).trans (hK p r))
    calc ∫ P in coarseInfo n k ⁻¹' S, finAvg (fun r => H (coarseInfo n k P) r) ∂pointSampleLaw n
        = ∫ P, finAvg (fun r => S.indicator (fun q => H q r) (coarseInfo n k P))
            ∂pointSampleLaw n := by
          rw [← integral_indicator (hc hS)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
          by_cases hP : coarseInfo n k P ∈ S <;> simp [hP, finAvg]
      _ = ∫ P, S.indicator (fun q => H q (freshInfo n k m hm P)) (coarseInfo n k P)
            ∂pointSampleLaw n := hcut.symm
      _ = ∫ P in coarseInfo n k ⁻¹' S, H (coarseInfo n k P) (freshInfo n k m hm P)
            ∂pointSampleLaw n := by
          rw [← integral_indicator (hc hS)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
          by_cases hP : coarseInfo n k P ∈ S <;> simp [hP]
  · -- the average is a measurable function of the coarse information
    exact ((measurable_finAvg_coarse n m H hH).comp
      (comap_measurable (coarseInfo n k))).stronglyMeasurable.aestronglyMeasurable

end

end R56Audit
end

section
/-!
# Summing Lemma 2.3 over the comparison rectangles of a transition

Auditor's supplement (not part of the audited archive).

Proof of Lemma 2.4: "Every old cell is a horizontal strip of exactly one comparison rectangle
`R = I × J`, and every new cell is a vertical strip of exactly one. So, with the children
`C_1, …, C_b` of `I` and the blocks `B_1, …, B_b` of `J` for each `R`,

`bM (Z_{j+1} - Z_j) = Σ_R (Σ_k osc_J a^{(C_k)} - Σ_ℓ osc_{B_ℓ} a^{(I)})`.

Conditionally on `𝓕_j`, the next digits perform the local experiment of Section 2.3 in every
`R` at once \[…\]. So Lemma 2.3 bounds the conditional expectation of each term, and dividing
by `bM` gives (11)."

`Zstep_gain` is this computation for fixed heights `V` and fixed stage-`j` indices `g`: the
average of `Z_{j+1}` over the next digits is at least `Z_j + δ_j`.

The comparison rectangle `R = I × J` with the index `(c, v)`, `c < b^j` and `v < b^{h-j-1}`,
has the `c`-th horizontal interval of stage `j` as `I` and the `v`-th vertical interval of
stage `j+1` as `J`. The two halves of the displayed identity are

* `Zstep_eq_sum_blocks`: `Z_j = (1/(bM)) Σ_R Σ_ℓ osc_{B_ℓ} a^{(I)}` (the old cells);
* `Zstep_succ_eq_sum_children`: `Z_{j+1} = (1/(bM)) Σ_R Σ_k osc_J a^{(C_k)}` (the new cells),
  where the endpoint average of the child `C_{k+1}` of `I`, the interval `b c + k` of stage
  `j+1`, is the child function of the local experiment (`childAvg_sideIdx`).
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-- The points of the inner region of the comparison rectangle `R = I × J` of the transition
`j → j+1`, where `I` is the `c`-th horizontal interval of stage `j` and `J` the `v`-th
vertical interval of stage `j+1`: the points with stage-`j` index `c` whose height lies in
`J` without its bottom and top blocks. -/
def innerSet (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) (c v : ℕ) : Finset (Fin n) :=
  innerPoints b V (fun i => sideIdx (g i) c) ((v : ℝ) * vlen b h (j + 1)) (vlen b h j)

/-- `δ_j = (1/(4bM)) Σ_R √(m_R)` of display (11), read from the heights and the indices. -/
def deltaStep (b h j : ℕ) (V : Fin n → ℝ) (g : Fin n → ℤ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
      Real.sqrt ((innerSet b h j V g c v).card)) / (4 * (b : ℝ) * (b : ℝ) ^ (h - 1))

/-- The numbers below `b ^ (m + 1)` are the numbers `b v + ℓ` with `v < b ^ m` and `ℓ < b`. -/
lemma sum_fin_pow_eq_sum_mul_add (b : ℕ) {e m : ℕ} (he : e = m + 1) (f : ℕ → ℝ) :
    ∑ w : Fin (b ^ e), f w = ∑ v : Fin (b ^ m), ∑ ℓ : Fin b, f (b * v + ℓ) := by
  subst he
  rw [Fin.sum_univ_eq_sum_range f (b ^ (m + 1)), pow_succ,
    ← Fin.sum_univ_eq_sum_range f (b ^ m * b), ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun ℓ _ => ?_
  rw [finProdFinEquiv_apply_val, add_comm]

/-- The weight in the child `C_{κ+1}` of the interval `c` is that in the interval `b c + κ`. -/
lemma childWeight_sideIdx {b : ℕ} (G : ℤ) (c : ℕ) (ρ κ : Fin b) :
    childWeight (sideIdx G c) ρ κ =
      oldWeight (sideIdx ((b : ℤ) * G + ((ρ : ℕ) : ℤ)) (b * c + κ)) := by
  have hρ : ((ρ : ℕ) : ℤ) < b := by exact_mod_cast ρ.isLt
  have hκ : ((κ : ℕ) : ℤ) < b := by exact_mod_cast κ.isLt
  unfold sideIdx
  rw [Nat.cast_add, Nat.cast_mul]
  rcases lt_trichotomy G (c : ℤ) with hG | rfl | hG
  · -- to the left of `I`, hence to the left of every child
    have h1 : (b : ℤ) * G + (ρ : ℕ) < (b : ℤ) * c + (κ : ℕ) := by nlinarith
    rw [ite_eq_left hG, ite_eq_left h1]
    rfl
  · -- in `I`: the next digit `ρ` is compared with `κ`
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    change (if ρ < κ then (1 : ℝ) else if ρ = κ then 1 / 2 else 0) = _
    rcases lt_trichotomy ρ κ with hr | rfl | hr
    · have h1 : (b : ℤ) * c + (ρ : ℕ) < (b : ℤ) * c + (κ : ℕ) := by omega
      rw [ite_eq_left hr, ite_eq_left h1]
      rfl
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_right (lt_irrefl _),
        ite_eq_left rfl]
      rfl
    · have h1 : (b : ℤ) * c + (κ : ℕ) < (b : ℤ) * c + (ρ : ℕ) := by omega
      rw [ite_eq_right (lt_asymm hr), ite_eq_right hr.ne', ite_eq_right (lt_asymm h1),
        ite_eq_right h1.ne']
      rfl
  · -- to the right of `I`, hence to the right of every child
    have h1 : (b : ℤ) * c + (κ : ℕ) < (b : ℤ) * G + (ρ : ℕ) := by nlinarith
    rw [ite_eq_right (lt_asymm hG), ite_eq_right hG.ne', ite_eq_right (lt_asymm h1),
      ite_eq_right h1.ne']
    rfl

/-- The child function `a_{k+1}` of `I` is the endpoint average of the interval `b c + k`. -/
lemma childAvg_sideIdx {b : ℕ} (ε V : Fin n → ℝ) (g : Fin n → ℤ) (c : ℕ)
    (r : Fin n → Fin b) (k : Fin b) :
    childAvg ε V (fun i => sideIdx (g i) c) r k =
      endpointAvg ε V (fun i => sideIdx (refineIdx g r i) (b * c + k)) := by
  funext y
  refine stepFn_congr V (fun i => ?_) y
  change ε i * childWeight (sideIdx (g i) c) (r i) k =
    ε i * oldWeight (sideIdx ((b : ℤ) * g i + ((r i : ℕ) : ℤ)) (b * c + k))
  rw [childWeight_sideIdx]

/-- `Z_j = (1/(bM)) Σ_R Σ_ℓ osc_{B_ℓ} a^{(I)}`: an old cell is a horizontal strip of one `R`. -/
lemma Zstep_eq_sum_blocks {b h j : ℕ} (hj : j < h) (ε V : Fin n → ℝ) (g : Fin n → ℤ) :
    Zstep ε b h j V g =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ ℓ : Fin b,
        osc (block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ)
          (endpointAvg ε V (fun i => sideIdx (g i) c))) / (b : ℝ) ^ h := by
  unfold Zstep
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  -- the vertical intervals of stage `j` are the blocks `b v + ℓ` of those of stage `j + 1`
  rw [sum_fin_pow_eq_sum_mul_add b (by omega : h - j = h - j - 1 + 1)
    (fun w => osc (vcell b h j w) (endpointAvg ε V (fun i => sideIdx (g i) c)))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun ℓ _ => ?_
  rw [vcell_eq_block]

/-- `Z_{j+1} = (1/(bM)) Σ_R Σ_k osc_J a^{(C_k)}`: a new cell is a vertical strip of one `R`. -/
lemma Zstep_succ_eq_sum_children {b : ℕ} (h j : ℕ) (ε V : Fin n → ℝ) (g : Fin n → ℤ)
    (r : Fin n → Fin b) :
    Zstep ε b h (j + 1) V (refineIdx g r) =
      (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), ∑ k : Fin b,
        osc (Set.Ico ((v : ℝ) * vlen b h (j + 1)) ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j))
          (childAvg ε V (fun i => sideIdx (g i) c) r k)) / (b : ℝ) ^ h := by
  unfold Zstep
  congr 1
  -- the horizontal intervals of stage `j + 1` are the children `b c + k` of those of stage `j`
  rw [Nat.sub_add_eq, sum_fin_pow_eq_sum_mul_add b rfl (fun w => ∑ v : Fin (b ^ (h - j - 1)),
    osc (vcell b h (j + 1) v) (endpointAvg ε V (fun i => sideIdx (refineIdx g r i) w)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
  rw [vcell_succ_eq, childAvg_sideIdx]

/-- **Lemma 2.4 for fixed heights and stage-`j` indices**: the average of `Z_{j+1}` over the
next digits is at least `Z_j + δ_j`. -/
theorem Zstep_gain {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| = 1) (V : Fin n → ℝ) (g : Fin n → ℤ) :
    Zstep ε b h j V g + deltaStep b h j V g ≤
      finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) V (refineIdx g r)) := by
  have hb0 : 0 < b := by omega
  -- `4bM = 4b^h`
  have hbM : 4 * (b : ℝ) * (b : ℝ) ^ (h - 1) = 4 * (b : ℝ) ^ h := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ h)]
  -- `Z_j + δ_j`, as a sum over the comparison rectangles (the old cells)
  calc Zstep ε b h j V g + deltaStep b h j V g
      = (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
          (∑ ℓ : Fin b, osc (block ((v : ℝ) * vlen b h (j + 1)) (vlen b h j) ℓ)
              (endpointAvg ε V (fun i => sideIdx (g i) c)) +
            (1 / 4) * Real.sqrt (innerSet b h j V g c v).card)) / (b : ℝ) ^ h := by
        rw [Zstep_eq_sum_blocks hj, deltaStep, hbM]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    -- Lemma 2.3 in every comparison rectangle
    _ ≤ (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
          finAvg (fun r : Fin n → Fin b => ∑ k : Fin b,
            osc (Set.Ico ((v : ℝ) * vlen b h (j + 1))
                ((v : ℝ) * vlen b h (j + 1) + b * vlen b h j))
              (childAvg ε V (fun i => sideIdx (g i) c) r k))) / (b : ℝ) ^ h :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun v _ =>
          local_gain hb ε hε V _ _ (vlen_pos hb0 h j)) (by positivity)
    -- the new cells; the average of a sum is the sum of the averages
    _ = finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) V (refineIdx g r)) := by
        simp_rw [Zstep_succ_eq_sum_children, finAvg_div_const, finAvg_sum]

end

end R56Audit
end

section
/-!
# The σ-fields `𝓕_j` and the potential as a process

Auditor's supplement (not part of the audited archive).

Section 2.4: "Let `𝓕_j` be the σ-field generated by all heights and by the first `j` base-`b`
digits of every horizontal coordinate. The first `j` digits of `U_i` determine the stage-`j`
horizontal interval that contains `U_i`. So `Z_j` is `𝓕_j`-measurable. The `(j+1)`-st digits,
which we call the next digits at stage `j`, are independent and uniform conditional on `𝓕_j`."

| Manuscript | Here |
| --- | --- |
| `𝓕_j` | `stageSigma n b j`, generated by the heights and the stage-`j` indices |
| the filtration `(𝓕_j)` | `stageFiltration n b hb` |
| the next digits at stage `j` | `freshInfo n (b^j) b hb` |
| `Z_j` as a function of the sample | `Zproc ε b h j` (for `j ≤ h`) |
| `E[Z_{j+1} | 𝓕_j]` | `Zmean ε b h j` (`condExp_Zproc_succ`) |

The σ-field `stageSigma n b j` is generated by the heights and by the index of the stage-`j`
horizontal interval `(c b^{-j}, (c+1) b^{-j}]` that contains each `U_i`. The manuscript works
"on the probability-one event that \[…\] no coordinate of a point has the form `k/b^r`"; on
this event the index is the integer whose base-`b` expansion consists of the first `j` digits
of `U_i`. `Digits.lean` proves that conditional expectations given the σ-field generated by
the heights and the digits themselves are almost surely the same.

* `stageFiltration`: the σ-fields increase with `j`;
* `Zproc_stronglyMeasurable`: `Z_j` is `𝓕_j`-measurable;
* `iIndepFun_fresh`, `indepFun_coarse_fresh`: the next digits are independent of each other
  and of `𝓕_j` (Step 2 of the proof of Lemma 2.6);
* `condExp_Zproc_succ`: `E[Z_{j+1} | 𝓕_j]` is the average of `Z_{j+1}` over the next digits;
* `Zmean_ge`: this average is at least `Z_j + δ_j` (Lemma 2.3 in every comparison rectangle);
* `Zpot_ae_eq_Zproc`: almost surely `Zproc` is the potential `Zpot` of the manuscript.
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets Oscillation

noncomputable section

variable {n : ℕ}

/-! ### The σ-fields -/

/-- `𝓕_j`: the σ-field generated by all heights and by the stage-`j` indices of all horizontal
coordinates. -/
abbrev stageSigma (n b j : ℕ) : MeasurableSpace (Fin n → ℝ × ℝ) :=
  MeasurableSpace.comap (coarseInfo n (b ^ j)) inferInstance

lemma stageSigma_le (n b j : ℕ) :
    stageSigma n b j ≤ (inferInstance : MeasurableSpace (Fin n → ℝ × ℝ)) :=
  (measurable_coarseInfo n (b ^ j)).comap_le

/-- The heights and indices of stage `j + 1` are those of stage `j` together with the next
digits. -/
lemma coarseInfo_succ {b : ℕ} (hb : 0 < b) (j : ℕ) (P : Fin n → ℝ × ℝ) :
    coarseInfo n (b ^ (j + 1)) P =
      ((coarseInfo n (b ^ j) P).1,
        refineIdx (coarseInfo n (b ^ j) P).2 (freshInfo n (b ^ j) b hb P)) :=
  Prod.ext rfl (funext fun i => gridIndex_succ hb j (P i).1)

/-- `𝓕_j ⊆ 𝓕_{j+1}`. -/
lemma stageSigma_succ_le {b : ℕ} (hb : 0 < b) (n j : ℕ) :
    stageSigma n b j ≤ stageSigma n b (j + 1) := by
  refine MeasurableSpace.comap_le_comap_of_eq_comp
    (fun p : (Fin n → ℝ) × (Fin n → ℤ) => (p.1, fun i => p.2 i / (b : ℤ)))
    (measurable_fst.prodMk ((measurable_of_countable
      (fun g : Fin n → ℤ => fun i => g i / (b : ℤ))).comp measurable_snd)) ?_
  funext P
  refine Prod.ext rfl (funext fun i => ?_)
  change gridIndex (b ^ j) (P i).1 = gridIndex (b ^ (j + 1)) (P i).1 / (b : ℤ)
  rw [pow_succ]
  exact (gridIndex_mul_ediv (b ^ j) b hb (P i).1).symm

/-- The filtration `(𝓕_j)_{j ≥ 0}`. -/
def stageFiltration (n b : ℕ) (hb : 0 < b) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ × ℝ)) where
  seq j := stageSigma n b j
  mono' := monotone_nat_of_le_succ fun j => stageSigma_succ_le hb n j
  le' j := stageSigma_le n b j

lemma stageSigma_mono {b : ℕ} (hb : 0 < b) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    stageSigma n b i ≤ stageSigma n b j :=
  (stageFiltration n b hb).mono hij

/-! ### The potential as a process -/

/-- The potential at stage `min j h`, as a function of the sample. For `j ≤ h` this is `Z_j`
(`Zproc_eq`, `Zpot_ae_eq_Zproc`). -/
def Zproc (ε : Fin n → ℝ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  Zstep ε b h (min j h) (coarseInfo n (b ^ min j h) P).1 (coarseInfo n (b ^ min j h) P).2

/-- The average of `Z_{j+1}` over all values of the next digits, given the heights and the
stage-`j` indices. -/
def Zmean (ε : Fin n → ℝ) (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  finAvg (fun r : Fin n → Fin b =>
    Zstep ε b h (j + 1) (coarseInfo n (b ^ j) P).1 (refineIdx (coarseInfo n (b ^ j) P).2 r))

lemma Zproc_eq {b h j : ℕ} (hj : j ≤ h) (ε : Fin n → ℝ) (P : Fin n → ℝ × ℝ) :
    Zproc ε b h j P =
      Zstep ε b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2 := by
  unfold Zproc
  rw [min_eq_left hj]

/-- `Z_{j+1}` is a function of the heights, the stage-`j` indices and the next digits. -/
lemma Zproc_succ {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ) (P : Fin n → ℝ × ℝ) :
    Zproc ε b h (j + 1) P =
      Zstep ε b h (j + 1) (coarseInfo n (b ^ j) P).1
        (refineIdx (coarseInfo n (b ^ j) P).2 (freshInfo n (b ^ j) b hb P)) := by
  rw [Zproc_eq (by omega : j + 1 ≤ h), coarseInfo_succ hb]

/-- The stage-`(j+1)` potential as a measurable function of the heights and stage-`j`
indices, for fixed next digits. -/
lemma measurable_Zstep_refine {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ)
    (r : Fin n → Fin b) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℤ) => Zstep ε b h j p.1 (refineIdx p.2 r)) := by
  have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℤ) => (p.1, refineIdx p.2 r)) :=
    measurable_fst.prodMk
      ((measurable_of_countable (fun g : Fin n → ℤ => refineIdx g r)).comp measurable_snd)
  have h3 := (measurable_Zstep_uncurry hb ε h j).comp h2
  exact h3

/-- **`Z_j` is `𝓕_j`-measurable.** -/
theorem Zproc_stronglyMeasurable {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    StronglyMeasurable[stageSigma n b j] (Zproc ε b h j) := by
  have h1 : Measurable[stageSigma n b (min j h)] (Zproc ε b h j) :=
    (measurable_Zstep_uncurry hb ε h (min j h)).comp (comap_measurable _)
  exact (h1.mono (stageSigma_mono hb n (min_le_left j h)) le_rfl).stronglyMeasurable

lemma measurable_Zproc {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (Zproc ε b h j) :=
  ((Zproc_stronglyMeasurable hb ε h j).mono (stageSigma_le n b j)).measurable

/-- The average over the next digits is `𝓕_j`-measurable. -/
theorem Zmean_stronglyMeasurable {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    StronglyMeasurable[stageSigma n b j] (Zmean ε b h j) := by
  have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℤ) =>
      finAvg (fun r : Fin n → Fin b => Zstep ε b h (j + 1) p.1 (refineIdx p.2 r))) :=
    (Finset.measurable_sum _ fun r _ => measurable_Zstep_refine hb ε h (j + 1) r).div_const _
  exact (h1.comp (comap_measurable _)).stronglyMeasurable

lemma measurable_Zmean {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (Zmean ε b h j) :=
  ((Zmean_stronglyMeasurable hb ε h j).mono (stageSigma_le n b j)).measurable

lemma Zproc_nonneg {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (P : Fin n → ℝ × ℝ) :
    0 ≤ Zproc ε b h j P :=
  Zstep_nonneg hb ε h _ _ _

lemma Zproc_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h j : ℕ)
    (P : Fin n → ℝ × ℝ) : Zproc ε b h j P ≤ n :=
  Zstep_le hb (min_le_right j h) ε hε _ _

lemma abs_Zproc_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h j : ℕ)
    (P : Fin n → ℝ × ℝ) : |Zproc ε b h j P| ≤ n :=
  abs_Zstep_le hb (min_le_right j h) ε hε _ _

lemma Zmean_nonneg {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) (P : Fin n → ℝ × ℝ) :
    0 ≤ Zmean ε b h j P :=
  finAvg_nonneg fun _ => Zstep_nonneg hb ε h _ _ _

lemma Zmean_le {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (P : Fin n → ℝ × ℝ) : Zmean ε b h j P ≤ n := by
  have : Nonempty (Fin n → Fin b) := ⟨fun _ => ⟨0, hb⟩⟩
  exact (finAvg_mono fun r => Zstep_le hb (by omega : j + 1 ≤ h) ε hε _ _).trans_eq
    (finAvg_const _)

lemma integrable_Zproc {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h j : ℕ) :
    Integrable (Zproc ε b h j) (pointSampleLaw n) :=
  Integrable.of_bound (measurable_Zproc hb ε h j).aestronglyMeasurable n
    (Filter.Eventually.of_forall fun P => by
      rw [Real.norm_eq_abs]
      exact abs_Zproc_le hb ε hε h j P)

/-! ### The next digits -/

/-- **The next digits are independent of each other** (they are functions of different
points). -/
theorem iIndepFun_fresh (n k m : ℕ) (hm : 0 < m) :
    iIndepFun (fun (i : Fin n) (P : Fin n → ℝ × ℝ) => freshGridIndex k m hm (P i).1)
      (pointSampleLaw n) :=
  iIndepFun_pi (X := fun (_ : Fin n) (z : ℝ × ℝ) => freshGridIndex k m hm z.1)
    fun _ => ((measurable_freshGridIndex k m hm).comp measurable_fst).aemeasurable

/-- The joint probability of an event of `𝓕` (given by a measurable set `s` of heights and
indices) and of a set `t` of values of the next digits. -/
lemma measureReal_coarse_inter_fresh (n k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    {s : Set ((Fin n → ℝ) × (Fin n → ℤ))} (hs : MeasurableSet s) (t : Set (Fin n → Fin m)) :
    (pointSampleLaw n).real (coarseInfo n k ⁻¹' s ∩ freshInfo n k m hm ⁻¹' t) =
      (pointSampleLaw n).real (coarseInfo n k ⁻¹' s) *
        finAvg (t.indicator (fun _ => (1 : ℝ))) := by
  classical
  have hc := measurable_coarseInfo n k
  have hf := measurable_freshInfo n k m hm
  have key := integral_fresh_given_heights n k m hk hm
    (fun p r => s.indicator (fun _ => (1 : ℝ)) p * t.indicator (fun _ => (1 : ℝ)) r)
    (fun r => (measurable_const.indicator hs).mul_const _) 1
    (fun p r => by
      rw [abs_mul]
      have h1 : |s.indicator (fun _ => (1 : ℝ)) p| ≤ 1 := by
        by_cases hp : p ∈ s <;> simp [hp]
      have h2 : |t.indicator (fun _ => (1 : ℝ)) r| ≤ 1 := by
        by_cases hr : r ∈ t <;> simp [hr]
      calc |s.indicator (fun _ => (1 : ℝ)) p| * |t.indicator (fun _ => (1 : ℝ)) r| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  have hL : ∫ P, s.indicator (fun _ => (1 : ℝ)) (coarseInfo n k P) *
      t.indicator (fun _ => (1 : ℝ)) (freshInfo n k m hm P) ∂pointSampleLaw n =
      (pointSampleLaw n).real (coarseInfo n k ⁻¹' s ∩ freshInfo n k m hm ⁻¹' t) := by
    rw [← integral_indicator_one ((hc hs).inter (hf (MeasurableSet.of_discrete (s := t))))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
    by_cases h1 : coarseInfo n k P ∈ s <;> by_cases h2 : freshInfo n k m hm P ∈ t <;>
      simp [Set.indicator, h1, h2]
  have hR : ∫ P, finAvg (fun r => s.indicator (fun _ => (1 : ℝ)) (coarseInfo n k P) *
      t.indicator (fun _ => (1 : ℝ)) r) ∂pointSampleLaw n =
      (pointSampleLaw n).real (coarseInfo n k ⁻¹' s) *
        finAvg (t.indicator (fun _ => (1 : ℝ))) := by
    simp_rw [finAvg_const_mul]
    rw [integral_mul_const, ← integral_indicator_one (hc hs)]
    congr 1
  rw [← hL, key, hR]

/-- **The next digits are independent of `𝓕`**: of the heights and the indices. -/
theorem indepFun_coarse_fresh (n k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    IndepFun (coarseInfo n k) (freshInfo n k m hm) (pointSampleLaw n) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs _
  have h1 := measureReal_coarse_inter_fresh n k m hk hm hs t
  have h2 := measureReal_coarse_inter_fresh n k m hk hm MeasurableSet.univ t
  simp only [Set.preimage_univ, Set.univ_inter, probReal_univ, one_mul] at h2
  rw [← h2] at h1
  have h3 : ((pointSampleLaw n) (coarseInfo n k ⁻¹' s ∩ freshInfo n k m hm ⁻¹' t)).toReal =
      ((pointSampleLaw n) (coarseInfo n k ⁻¹' s) *
        (pointSampleLaw n) (freshInfo n k m hm ⁻¹' t)).toReal := by
    rw [ENNReal.toReal_mul]
    exact h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp h3

/-! ### The conditional expectation of the next potential -/

/-- **`E[Z_{j+1} | 𝓕_j]` is the average of `Z_{j+1}` over the next digits**, almost surely. -/
theorem condExp_Zproc_succ {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (pointSampleLaw n)[Zproc ε b h (j + 1) | stageSigma n b j] =ᵐ[pointSampleLaw n]
      Zmean ε b h j := by
  have key := condExp_fresh_given_heights n (b ^ j) b (pow_pos hb j) hb
    (fun p r => Zstep ε b h (j + 1) p.1 (refineIdx p.2 r))
    (fun r => measurable_Zstep_refine hb ε h (j + 1) r) n
    (fun p r => abs_Zstep_le hb (by omega : j + 1 ≤ h) ε hε _ _)
  have he : Zproc ε b h (j + 1) = fun P => Zstep ε b h (j + 1) (coarseInfo n (b ^ j) P).1
      (refineIdx (coarseInfo n (b ^ j) P).2 (freshInfo n (b ^ j) b hb P)) :=
    funext fun P => Zproc_succ hb hj ε P
  rw [he]
  exact key

/-- **Lemma 2.3 in every comparison rectangle**: the average of `Z_{j+1}` over the next
digits is at least `Z_j + δ_j`. -/
theorem Zmean_ge {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1)
    (P : Fin n → ℝ × ℝ) :
    Zproc ε b h j P +
        deltaStep b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2 ≤
      Zmean ε b h j P := by
  rw [Zproc_eq hj.le]
  exact Zstep_gain hb hj ε hε _ _

/-! ### The potential of the manuscript -/

/-- Almost surely, `Zproc` is the potential `Z_j` of the manuscript (display (1)). -/
theorem Zpot_ae_eq_Zproc {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ) :
    Zpot χ b h j =ᵐ[pointSampleLaw n] Zproc (sgn χ) b h j := by
  filter_upwards [ae_pointSampleLaw_mem_Ioc n] with P hP
  rw [Zpot_eq_Zstep hb χ h j P fun i => ⟨(hP i).1.1.le, (hP i).2.1.le⟩, Zproc_eq hj]
  rfl

end

end R56Audit
end

section
/-!
# Good transitions: the regions, `δ_j`, `δ_*`, Lemma 2.5(i), and the event of Section 2.1

Auditor's supplement (not part of the audited archive).

In the transition `j → j+1`, the comparison rectangle with indices `(c, v)` is `R = I × J`,
where `I = [c b^{-j}, (c+1) b^{-j}]` is the `c`-th horizontal interval of stage `j` and
`J = [v b^{j+1-h}, (v+1) b^{j+1-h})` the `v`-th vertical interval of stage `j+1`; it consists
of `b` old cells of height `b^{j-h}`. Horizontal intervals are closed and vertical intervals
are closed at the bottom and open at the top, as in the manuscript.

| Manuscript | Here |
| --- | --- |
| inner region `R^in`: `R` without its bottom and top old cells | `innerRegion b h j c v` |
| `m_R` | `innerCount b h j P c v` |
| `R^in` is heavy: `m_R > bn/M`, `M = b^{h-1}` | `Heavy b h j P c v` |
| the transition is good: at least `n/2` points lie in inner regions that are not heavy | `GoodTransition b h j P` |
| `δ_j` of (11), `δ_*` of (12) | `delta b h j P`, `deltaStar n b h` |
| "all heights are distinct" | `Function.Injective fun i => (P i).2` |
| "no coordinate of a point has the form `k/b^r`" | `NoGrid b P` |
| the probability-one event of Section 2.1 | `SetupEvent b P` |

* `lemma_2_5_i`: **Lemma 2.5(i)**, on `G_j` we have `δ_j ≥ δ_*`. This is a statement about
  the numbers of points in the regions, for every position of the points; the proof is the
  one of the manuscript.
* `measurableSet_goodTransition`: the events `G_j` are measurable.

Lemma 2.5(ii) is proved in `Crowding.lean`. (`StageGeometry.lean` identifies `innerRegion`
with the comparison rectangle without its bottom and top old cells.)

**The probability-one event of Section 2.1**: "all heights are distinct and \[…\] no
coordinate of a point has the form `k/b^r` with integers `k` and `r ≥ 0`" is `SetupEvent b P`;
it has probability one (`ae_setupEvent`). The points of the manuscript lie in `[0,1]²`; on
this event their coordinates then lie in `(0,1)`, since `0 = 0/b^0` and `1 = 1/b^0`
(`inUnit_of_noGrid`). The supplement uses the two halves of the event separately, and only
where they are needed; `InUnit` (all coordinates in `(0,1]`) holds almost surely for the
law `unifPts n` (`ae_inUnit`).
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Oscillation

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### Regions, counts, good transitions -/

/-- The inner region `R^in` of the comparison rectangle `R = I × J` of the transition
`j → j+1`, with `I = [c b^{-j}, (c+1) b^{-j}]` and `J = [v b^{j+1-h}, (v+1) b^{j+1-h})`: the
points of `R` whose height lies in `J` without its bottom and top blocks of length `b^{j-h}`,
that is, in `[v b^{j+1-h} + b^{j-h}, (v+1) b^{j+1-h} - b^{j-h})`. -/
def innerRegion (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)
      ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)

/-- `m_R`: the number of points in the inner region of `R`. -/
def innerCount (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => P i ∈ innerRegion b h j c v)).card

/-- The inner region is heavy: `m_R > b n / M`, with `M = b^{h-1}`. -/
def Heavy (b h j : ℕ) (P : Fin n → ℝ × ℝ) (c v : ℕ) : Prop :=
  (b : ℝ) * n / (b : ℝ) ^ (h - 1) < innerCount b h j P c v

/-- The transition `j → j+1` is good: at least `n/2` points lie in inner regions that are
not heavy. -/
def GoodTransition (b h j : ℕ) (P : Fin n → ℝ × ℝ) : Prop :=
  (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
    P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)).card

/-- `δ_j = (1 / (4bM)) Σ_R √(m_R)`, display (11). -/
def delta (b h j : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  (∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P c v)) /
    (4 * (b : ℝ) * (b : ℝ) ^ (h - 1))

/-- `δ_* = (1 / (8 b^{3/2})) √(n/M)`, display (12). -/
def deltaStar (n b h : ℕ) : ℝ :=
  1 / (8 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))

/-! ### Lemma 2.5(i) -/

/-- `x^{3/2} = x √x` for `x ≥ 0`. -/
lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | h
  · rw [Real.zero_rpow (by norm_num), zero_mul]
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

/-- **Lemma 2.5(i).** On `G_j` we have `δ_j ≥ δ_*`.

"An inner region that is not heavy has `m_R ≤ bn/M`, and hence `√(m_R) ≥ m_R / √(bn/M)`. On
`G_j` these regions hold at least `n/2` points in total, so `Σ_R √(m_R) ≥ (n/2) √(M/(bn))`."

No condition on the position of the points. -/
theorem lemma_2_5_i {b h j : ℕ} (hn : 0 < n) (hb : 0 < b) (P : Fin n → ℝ × ℝ)
    (hG : GoodTransition b h j P) : deltaStar n b h ≤ delta b h j P := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  -- the threshold `T = bn/M` for heavy regions
  have hT : (0 : ℝ) < (b : ℝ) * n / (b : ℝ) ^ (h - 1) := by positivity
  have hsT : 0 < Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) := Real.sqrt_pos.mpr hT
  -- a region that is not heavy has `√m ≥ m / √T`
  have hsqrt : ∀ (c : Fin (b ^ j)) (v : Fin (b ^ (h - j - 1))), ¬ Heavy b h j P c v →
      (innerCount b h j P c v : ℝ) / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) ≤
        Real.sqrt (innerCount b h j P c v) := by
    intro c v hnh
    have hle : (innerCount b h j P c v : ℝ) ≤ (b : ℝ) * n / (b : ℝ) ^ (h - 1) := not_lt.mp hnh
    have hm0 : (0 : ℝ) ≤ innerCount b h j P c v := Nat.cast_nonneg _
    rw [div_le_iff₀ hsT]
    calc (innerCount b h j P c v : ℝ)
        = Real.sqrt (innerCount b h j P c v) * Real.sqrt (innerCount b h j P c v) :=
          (Real.mul_self_sqrt hm0).symm
      _ ≤ Real.sqrt (innerCount b h j P c v) * Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)
  -- the regions that are not heavy hold at least `n/2` points in total
  let S : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))) :=
    Finset.univ.filter (fun p => ¬ Heavy b h j P p.1 p.2)
  have hcount : (n : ℝ) / 2 ≤ ∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ) := by
    refine hG.trans ?_
    have hsub : (Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)) ⊆
        S.biUnion (fun p => Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)) := by
      intro i hi
      obtain ⟨c, v, hin, hnh⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_biUnion.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnh⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩⟩
    have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have : ((Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)).card : ℝ) ≤
        ((∑ p ∈ S, (Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)).card : ℕ) : ℝ) :=
      by exact_mod_cast hcard
    refine this.trans (le_of_eq ?_)
    push_cast
    rfl
  -- hence `Σ_R √(m_R) ≥ (n/2) / √T`
  have hsum : (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) ≤
      ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P c v) := by
    calc (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1))
        ≤ (∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ)) /
            Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) :=
          div_le_div_of_nonneg_right hcount hsT.le
      _ = ∑ p ∈ S, (innerCount b h j P p.1 p.2 : ℝ) /
            Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) := Finset.sum_div _ _ _
      _ ≤ ∑ p ∈ S, Real.sqrt (innerCount b h j P p.1 p.2) :=
          Finset.sum_le_sum fun p hp => hsqrt p.1 p.2 (Finset.mem_filter.mp hp).2
      _ ≤ ∑ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)), Real.sqrt (innerCount b h j P p.1 p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun p _ _ => Real.sqrt_nonneg _
      _ = ∑ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j - 1)),
            Real.sqrt (innerCount b h j P c v) := Fintype.sum_prod_type _
  -- `δ_* = (n/2) / √T / (4bM)`
  have hstar : deltaStar n b h =
      (n : ℝ) / 2 / Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) /
        (4 * (b : ℝ) * (b : ℝ) ^ (h - 1)) := by
    have hq : (0 : ℝ) < n / (b : ℝ) ^ (h - 1) := by positivity
    have hsq : 0 < Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) := Real.sqrt_pos.mpr hq
    have hsb : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr hbR
    have e1 : Real.sqrt ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) =
        Real.sqrt b * Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) := by
      rw [mul_div_assoc, Real.sqrt_mul hbR.le]
    have e2 : (n : ℝ) = Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) *
        Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) * (b : ℝ) ^ (h - 1) := by
      rw [Real.mul_self_sqrt hq.le]
      field_simp
    unfold deltaStar
    rw [e1, rpow_three_halves_eq_mul_sqrt hbR.le]
    have hbs : Real.sqrt (b : ℝ) ≠ 0 := hsb.ne'
    have hqs : Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) ≠ 0 := hsq.ne'
    rw [div_div, div_div, eq_div_iff (by positivity)]
    nth_rewrite 3 [e2]
    field_simp
    norm_num
  rw [hstar]
  unfold delta
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-! ### Measurability -/

/-! ### The probability-one event of Section 2.1 -/

/-- All coordinates of all points lie in `(0, 1]`; this holds almost surely. -/
def InUnit (P : Fin n → ℝ × ℝ) : Prop :=
  ∀ i, (P i).1 ∈ Set.Ioc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ioc (0 : ℝ) 1

/-- "no coordinate of a point has the form `k/b^r` with integers `k` and `r ≥ 0`": no point
lies on a grid line. -/
def NoGrid (b : ℕ) (P : Fin n → ℝ × ℝ) : Prop :=
  ∀ i, ∀ (k : ℤ) (r : ℕ), (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ (P i).2 ≠ (k : ℝ) / (b : ℝ) ^ r

/-- Almost surely all coordinates of `n` independent uniform points lie in `(0,1]`. -/
theorem ae_inUnit (n : ℕ) : ∀ᵐ P ∂unifPts n, InUnit P := by
  rw [← pointSampleLaw_eq_unifPts]
  exact ae_pointSampleLaw_mem_Ioc n

/-- Almost surely no coordinate of `n` independent uniform points has the form `k/b^r`. -/
theorem ae_noGrid (n b : ℕ) : ∀ᵐ P ∂unifPts n, NoGrid b P := by
  rw [← pointSampleLaw_eq_unifPts]
  refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => ae_all_iff.mpr fun r => ?_
  have hI : ∀ᵐ x ∂μI, x ≠ (k : ℝ) / (b : ℝ) ^ r := by
    rw [ae_iff]
    simp
  have hprod : ∀ᵐ z ∂μI.prod μI,
      z.1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ z.2 ≠ (k : ℝ) / (b : ℝ) ^ r := by
    have hms : MeasurableSet {z : ℝ × ℝ |
        z.1 ≠ (k : ℝ) / (b : ℝ) ^ r ∧ z.2 ≠ (k : ℝ) / (b : ℝ) ^ r} :=
      (measurableSet_eq_fun measurable_fst measurable_const).compl.inter
        (measurableSet_eq_fun measurable_snd measurable_const).compl
    apply (Measure.ae_prod_iff_ae_ae hms).mpr
    filter_upwards [hI] with u hu
    filter_upwards [hI] with v hv
    exact ⟨hu, hv⟩
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μI.prod μI) (i := i) hprod

end

end R56Audit
end

section
/-!
# Lemma 2.4 of the manuscript (conditional gain) and the identity (10)

Auditor's supplement (not part of the audited archive).

**Lemma 2.4.** For every `0 ≤ j < h`, almost surely

`E[Z_{j+1} - Z_j | 𝓕_j] ≥ δ_j := (1 / (4bM)) Σ_R √(m_R)`,

where `R` ranges over the `M` comparison rectangles of the transition `j → j+1`.

Here `Z_j` is the potential `Zpot` of display (1), with its extrema over the continuum of
heights; `𝓕_j` is `stageSigma n b j`; the conditional expectation is Mathlib's `condExp` for
the law `unifPts n` of `n` independent uniform points of the unit square; and `δ_j` is
`delta b h j` with the regions of the manuscript (`GoodTransitions.lean`). The statements for
the σ-field `digitSigma n b j` generated by the heights and the first `j` digits, which is the
manuscript's `𝓕_j`, are `lemma_2_4_digits` and `roadmap_digits` in `Digits.lean`; they follow
from the statements of this file.

**Display (10).** `Z_h = Z_0 + Σ_{j<h} E[Z_{j+1} - Z_j | 𝓕_j] + T`, where
`T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` is the fluctuation term (`fluct`).

* `lemma_2_4`: Lemma 2.4. The proof is the manuscript's: Lemma 2.3 (`local_gain`) in every
  comparison rectangle (`Zstep_gain`, `Zmean_ge`), the next digits being independent and
  uniform conditional on `𝓕_j` (`condExp_Zproc_succ`).
* `roadmap`: display (10), almost surely.
* `Zpot_aestronglyMeasurable`, `condExp_Zpot_self`: "`Z_j` is `𝓕_j`-measurable".
* `delta_eq_deltaStep`: on the probability-one event that no point lies on a grid line, `δ_j`
  is determined by the heights and the stage-`j` indices.
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Oscillation

noncomputable section

variable {n : ℕ}

/-! ### `δ_j` in terms of the heights and the indices -/

/-- If no point lies on a grid line, the points of the inner region of the comparison
rectangle `(c, v)` are those with stage-`j` index `c` whose height lies in the inner blocks. -/
lemma innerCount_eq_card_innerSet {b : ℕ} (hb : 0 < b) (h j c v : ℕ) (P : Fin n → ℝ × ℝ)
    (hgrid : NoGrid b P) :
    innerCount b h j P c v =
      (innerSet b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2 c v).card := by
  classical
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have e1 : (v : ℝ) * vlen b h (j + 1) + vlen b h j =
      ((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h := by
    unfold vlen
    ring
  have e2 : (v : ℝ) * vlen b h (j + 1) + ((b : ℝ) - 1) * vlen b h j =
      (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h := by
    unfold vlen
    rw [pow_succ]
    ring
  unfold innerCount innerSet innerPoints
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change P i ∈ innerRegion b h j c v ↔
    sideIdx (gridIndex (b ^ j) (P i).1) c = Side.inside ∧
      (v : ℝ) * vlen b h (j + 1) + vlen b h j ≤ (P i).2 ∧
      (P i).2 < (v : ℝ) * vlen b h (j + 1) + ((b : ℝ) - 1) * vlen b h j
  rw [e1, e2, ← sideOf_grid hb j c (P i).1, sideOf_eq_inside_iff]
  have hx : (P i).1 ≠ (c : ℝ) / (b : ℝ) ^ j := by
    have := (hgrid i (c : ℤ) j).1
    push_cast at this
    exact this
  unfold innerRegion
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm hx), h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1.le, h2⟩, h3, h4⟩

/-- If no point lies on a grid line, `δ_j` is the number read from the heights and the
stage-`j` indices. -/
theorem delta_eq_deltaStep {b : ℕ} (hb : 0 < b) (h j : ℕ) (P : Fin n → ℝ × ℝ)
    (hgrid : NoGrid b P) :
    delta b h j P =
      deltaStep b h j (coarseInfo n (b ^ j) P).1 (coarseInfo n (b ^ j) P).2 := by
  unfold delta deltaStep
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun v _ => ?_
  rw [innerCount_eq_card_innerSet hb h j c v P hgrid]

/-! ### Conditional expectations of the potential -/

lemma integrable_Zpot {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ) :
    Integrable (Zpot χ b h j) (pointSampleLaw n) :=
  (integrable_Zproc hb (sgn χ) (fun i => (abs_sgn χ i).le) h j).congr
    (Zpot_ae_eq_Zproc hb hj χ).symm

/-- `E[Z_j | 𝓕_j] = Z_j` almost surely: `Z_j` is `𝓕_j`-measurable. -/
lemma condExp_Zpot_self {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) (χ : Fin n → ℤˣ) :
    (pointSampleLaw n)[Zpot χ b h j | stageSigma n b j] =ᵐ[pointSampleLaw n] Zpot χ b h j := by
  have hε : ∀ i, |sgn χ i| ≤ 1 := fun i => (abs_sgn χ i).le
  have h1 := condExp_congr_ae (m := stageSigma n b j) (Zpot_ae_eq_Zproc hb hj χ)
  have h2 : (pointSampleLaw n)[Zproc (sgn χ) b h j | stageSigma n b j] = Zproc (sgn χ) b h j :=
    condExp_of_stronglyMeasurable (stageSigma_le n b j)
      (Zproc_stronglyMeasurable hb (sgn χ) h j) (integrable_Zproc hb (sgn χ) hε h j)
  rw [h2] at h1
  exact h1.trans (Zpot_ae_eq_Zproc hb hj χ).symm

/-- `E[Z_{j+1} | 𝓕_j]` is the average of `Z_{j+1}` over the next digits, almost surely. -/
lemma condExp_Zpot_succ {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ) :
    (pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j] =ᵐ[pointSampleLaw n]
      Zmean (sgn χ) b h j :=
  (condExp_congr_ae (m := stageSigma n b j)
    (Zpot_ae_eq_Zproc hb (by omega : j + 1 ≤ h) χ)).trans
      (condExp_Zproc_succ hb hj (sgn χ) fun i => (abs_sgn χ i).le)

/-- The conditional gain is `E[Z_{j+1} | 𝓕_j] - Z_j`, almost surely. -/
lemma condExp_gain {b h j : ℕ} (hb : 0 < b) (hj : j < h) (χ : Fin n → ℤˣ) :
    (pointSampleLaw n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]
      =ᵐ[pointSampleLaw n]
      fun P => ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P - Zpot χ b h j P := by
  have h1 := condExp_sub (integrable_Zpot hb (by omega : j + 1 ≤ h) χ)
    (integrable_Zpot hb hj.le χ) (stageSigma n b j)
  filter_upwards [h1, condExp_Zpot_self hb hj.le χ] with P hP hself
  have hP' : ((pointSampleLaw n)[Zpot χ b h (j + 1) - Zpot χ b h j | stageSigma n b j]) P =
      ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P -
        ((pointSampleLaw n)[Zpot χ b h j | stageSigma n b j]) P := hP
  rw [← hself, ← hP']
  rfl

/-! ### Lemma 2.4 -/

/-- **Lemma 2.4 (conditional gain).** For every `0 ≤ j < h`, almost surely

`E[Z_{j+1} - Z_j | 𝓕_j] ≥ δ_j = (1 / (4bM)) Σ_R √(m_R)`,

for every integer base `b ≥ 2` (the manuscript has `b ≥ 3`) and every coloring. -/
theorem lemma_2_4 {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, delta b h j P ≤
      ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P := by
  have hb0 : 0 < b := by omega
  have hgrid := ae_noGrid n b
  rw [← pointSampleLaw_eq_unifPts] at hgrid ⊢
  filter_upwards [condExp_gain hb0 hj χ, condExp_Zpot_succ hb0 hj χ,
    Zpot_ae_eq_Zproc hb0 hj.le χ, hgrid] with P h1 h2 h3 h4
  rw [h1, h2, h3, delta_eq_deltaStep hb0 h j P h4]
  have := Zmean_ge hb hj (sgn χ) (abs_sgn χ) P
  linarith

/-! ### The fluctuation term and display (10) -/

/-- **The fluctuation term** `T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` of display (10). -/
def fluct (χ : Fin n → ℤˣ) (b h : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range h,
    (Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)

/-- **Display (10)**: `Z_h = Z_0 + Σ_{j<h} E[Z_{j+1} - Z_j | 𝓕_j] + T`, almost surely. -/
theorem roadmap {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, Zpot χ b h h P = Zpot χ b h 0 P +
      ∑ j ∈ Finset.range h,
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P +
      fluct χ b h P := by
  have hall : ∀ᵐ P ∂pointSampleLaw n, ∀ j ∈ Finset.range h,
      ((pointSampleLaw n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P =
        ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P - Zpot χ b h j P := by
    refine (ae_ball_iff (Finset.range h).countable_toSet).mpr fun j hj => ?_
    exact condExp_gain hb (Finset.mem_range.mp hj) χ
  unfold fluct
  rw [← pointSampleLaw_eq_unifPts]
  filter_upwards [hall] with P hP
  rw [Finset.sum_congr rfl hP, add_assoc, ← Finset.sum_add_distrib]
  have htel : ∑ j ∈ Finset.range h, (Zpot χ b h (j + 1) P - Zpot χ b h j P) =
      Zpot χ b h h P - Zpot χ b h 0 P :=
    Finset.sum_range_sub (fun j => Zpot χ b h j P) h
  have hcongr : ∑ j ∈ Finset.range h,
      (((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P - Zpot χ b h j P +
        (Zpot χ b h (j + 1) P -
          ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P)) =
      ∑ j ∈ Finset.range h, (Zpot χ b h (j + 1) P - Zpot χ b h j P) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hcongr, htel]
  ring

end

end R56Audit
end

section
/-!
# One digit of one point changes the potential by at most `1/M`

Auditor's supplement (not part of the audited archive).

Step 1 of the proof of Lemma 2.6: "Changing the next digit of one point `P_i` changes
`Z_{j+1}` by at most `1/M`. Indeed, the change moves `P_i` to another child of its stage-`j`
interval `I`. So the weight of `P_i` changes only in the `b` children of `I`, in each of them
by a number in `[-1,1]`. Hence the endpoint average of each child changes by a multiple of the
function `y ↦ 1{V_i ≤ y}`, with a factor in `[-1,1]`, and the endpoint average of no other
interval of stage `j+1` changes. Consider a cell `C × B` of stage `j+1`, where `C` is a child
of `I`. If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not
change, by shift invariance. If `V_i ∈ B`, the added function has oscillation at most `1` on
`B`, and `osc_B a^{(C)}` changes by at most `1`, by the reverse triangle inequality. The
second case occurs for `b` cells, one for each child. Since `Z_{j+1}` is the sum of the
oscillations over the `bM` cells, divided by `bM`, it changes by at most `b/(bM) = 1/M`."

`Zstep_update_le` is this statement, for fixed heights `V` and fixed stage-`j` indices `g`.
Its proof follows the sentences above:

* `refineIdx_mem_block`, `refineIdx_update_of_ne`: the change moves `P_i` to another child of
  `I`, and it moves no other point;
* `abs_oldWeight_sideIdx_sub_le`, `sum_ite_block_le`: the weight of `P_i` changes only in the
  `b` children of `I`, in each of them by a number in `[-1,1]`;
* `abs_osc_endpointAvg_sub_le`: one cell `C × B`, with the two cases of the manuscript. If
  `V_i ∉ B`, the added function is constant on `B` (`stepFn_single_eq_of_notMem` in
  `StepOsc.lean`), and the oscillation does not change, by shift invariance (`osc_add_const`).
  If `V_i ∈ B`, the added function has oscillation at most the size of its jump
  (`osc_stepFn_single_le`), and the oscillation changes by at most this much, by the reverse
  triangle inequality (`abs_osc_add_sub_le`);
* `sum_abs_osc_endpointAvg_sub_le`: `V_i` lies in at most one vertical interval `B` of the
  stage (`vcell_unique`), so the second case occurs for at most one cell of each child;
* `abs_Zstep_sub_le`: the sum of the oscillations over all cells changes by at most `b`.
-/

namespace R56Audit

open Finset Oscillation

noncomputable section

variable {n : ℕ}

/-! ### The weight of `P_i` changes only in the `b` children of `I` -/

/-- Two weights differ by at most `1`. -/
lemma abs_oldWeight_sub_le (sd sd' : Side) : |oldWeight sd' - oldWeight sd| ≤ 1 := by
  cases sd <;> cases sd' <;> simp only [oldWeight] <;> norm_num

/-- Two indices in a block `[m, m + b)` lie on the same side of every index outside the block. -/
lemma sideIdx_eq_of_block {m x x' : ℤ} {b c : ℕ} (hx : m ≤ x ∧ x < m + b)
    (hx' : m ≤ x' ∧ x' < m + b) (hc : ¬(m ≤ (c : ℤ) ∧ (c : ℤ) < m + b)) :
    sideIdx x c = sideIdx x' c := by
  unfold sideIdx
  split_ifs <;> first | rfl | omega

/-- A point moving within a block `[m, m + b)` changes weight only in the block, by at most `1`. -/
lemma abs_oldWeight_sideIdx_sub_le {m x x' : ℤ} {b : ℕ} (hx : m ≤ x ∧ x < m + b)
    (hx' : m ≤ x' ∧ x' < m + b) (c : ℕ) :
    |oldWeight (sideIdx x' c) - oldWeight (sideIdx x c)| ≤
      if m ≤ (c : ℤ) ∧ (c : ℤ) < m + b then 1 else 0 := by
  split_ifs with hc
  · exact abs_oldWeight_sub_le _ _
  · rw [sideIdx_eq_of_block hx' hx hc, sub_self, abs_zero]

/-- A block `[m, m + b)` contains at most `b` of the indices `0, …, N - 1`. -/
lemma sum_ite_block_le (N b : ℕ) (m : ℤ) :
    ∑ c : Fin N, (if m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b then (1 : ℝ) else 0) ≤ b := by
  -- the indices in the block inject into the interval `[m, m + b)` of integers
  have hcard := Finset.card_le_card_of_injOn (t := Finset.Ico m (m + b))
    (s := Finset.univ.filter fun c : Fin N => m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b)
    (fun c : Fin N => ((c : ℕ) : ℤ))
    (fun c hc => Finset.mem_Ico.mpr (Finset.mem_filter.mp hc).2)
    (fun c _ c' _ hcc => Fin.ext (Nat.cast_injective hcc))
  rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hcard
  rw [Finset.sum_boole]
  exact_mod_cast hcard

/-! ### The cells of one horizontal interval -/

/-- A height lies in at most one vertical interval of a stage. -/
lemma vcell_unique {b : ℕ} (hb : 0 < b) (h j : ℕ) {v v' : ℕ} {y : ℝ} (hv : y ∈ vcell b h j v)
    (hv' : y ∈ vcell b h j v') : v = v' := by
  have hL := (vlen_pos hb h j).le
  have h1 : (v : ℝ) < v' + 1 := lt_of_mul_lt_mul_right (hv.1.trans_lt hv'.2) hL
  have h2 : (v' : ℝ) < v + 1 := lt_of_mul_lt_mul_right (hv'.1.trans_lt hv.2) hL
  have h1' : v < v' + 1 := by exact_mod_cast h1
  have h2' : v' < v + 1 := by exact_mod_cast h2
  omega

/-- One cell `C × B`, with `B = [s, t)`: moving `P_i` changes `osc_B a` by at most
`|ε_i (w_i' - w_i)|`, and only if `V_i ∈ B`. The proof has the two cases of the manuscript:
"If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not change, by
shift invariance. If `V_i ∈ B`, the added function has oscillation at most `1` on `B`, and
`osc_B a^{(C)}` changes by at most `1`, by the reverse triangle inequality." Here the added
function is `ε_i (w_i' - w_i) 1{V_i ≤ ·}`, and the bound is `|ε_i (w_i' - w_i)|` in place of
`1`. -/
lemma abs_osc_endpointAvg_sub_le (ε V : Fin n → ℝ) {side side' : Fin n → Side} (i : Fin n)
    (hside : ∀ k, k ≠ i → side' k = side k) {s t : ℝ} (hst : s < t) :
    |osc (Set.Ico s t) (endpointAvg ε V side') - osc (Set.Ico s t) (endpointAvg ε V side)| ≤
      if V i ∈ Set.Ico s t then |ε i * (oldWeight (side' i) - oldWeight (side i))| else 0 := by
  have hB : (Set.Ico s t).Nonempty := ⟨s, le_rfl, hst⟩
  have hfin : ((endpointAvg ε V side) '' Set.Ico s t).Finite := stepFn_image_finite V _ _
  -- the endpoint average changes by a multiple of the function `y ↦ 1{V_i ≤ y}`
  have hadd : endpointAvg ε V side' = fun y => endpointAvg ε V side y +
      stepFn V (fun k => ε k * (oldWeight (side' k) - oldWeight (side k))) y := by
    funext y
    unfold endpointAvg
    rw [← stepFn_add]
    exact stepFn_congr V (fun k => by ring) y
  -- the added function has its only jump at the height `V_i`
  have hd : ∀ k, k ≠ i → ε k * (oldWeight (side' k) - oldWeight (side k)) = 0 :=
    fun k hk => by rw [hside k hk, sub_self, mul_zero]
  rw [hadd]
  rcases (Classical.em (V i ∈ Set.Ico s t)).symm with hi | hi
  · -- "If `V_i ∉ B`, the added function is constant on `B`, and `osc_B a^{(C)}` does not
    -- change, by shift invariance."
    -- On `B`, the added function is the constant `ε_i (w_i' - w_i)` if `V_i` lies below `B`,
    -- and the constant `0` if `V_i` lies above `B`.
    have hconst : ∀ y ∈ Set.Ico s t,
        endpointAvg ε V side y +
            stepFn V (fun k => ε k * (oldWeight (side' k) - oldWeight (side k))) y =
          endpointAvg ε V side y +
            if V i < s then ε i * (oldWeight (side' i) - oldWeight (side i)) else 0 :=
      fun y hy => by rw [stepFn_single_eq_of_notMem V _ i hd hi hy]
    -- shift invariance: adding a constant does not change the oscillation on `B`
    rw [osc_congr hconst, osc_add_const hB hfin, sub_self, abs_zero, ite_eq_right hi]
  · -- "If `V_i ∈ B`, the added function has oscillation at most `1` on `B`, and `osc_B a^{(C)}`
    -- changes by at most `1`, by the reverse triangle inequality."
    exact (abs_osc_add_sub_le hB hfin (stepFn_image_finite V _ _)).trans
      (osc_stepFn_single_le V _ i hd hst)

/-- The cells of one horizontal interval change by at most `|ε_i (w_i' - w_i)|` in total. -/
lemma sum_abs_osc_endpointAvg_sub_le {b : ℕ} (hb : 0 < b) (h j N : ℕ) (ε V : Fin n → ℝ)
    {side side' : Fin n → Side} (i : Fin n) (hside : ∀ k, k ≠ i → side' k = side k) :
    ∑ v : Fin N, |osc (vcell b h j v) (endpointAvg ε V side') -
        osc (vcell b h j v) (endpointAvg ε V side)| ≤
      |ε i * (oldWeight (side' i) - oldWeight (side i))| := by
  have hcell := fun v : Fin N => abs_osc_endpointAvg_sub_le ε V i hside (vcell_lt hb h j v)
  -- the oscillation does not change on the vertical intervals that do not contain `V_i`
  have hout : ∀ v : Fin N, V i ∉ vcell b h j v →
      |osc (vcell b h j v) (endpointAvg ε V side') -
        osc (vcell b h j v) (endpointAvg ε V side)| = 0 := fun v hv =>
    le_antisymm ((hcell v).trans (ite_eq_right hv).le) (abs_nonneg _)
  by_cases hex : ∃ v₀ : Fin N, V i ∈ vcell b h j v₀
  · -- `V_i` lies in the vertical interval `v₀`, and in no other
    obtain ⟨v₀, hv₀⟩ := hex
    rw [Finset.sum_eq_single_of_mem v₀ (Finset.mem_univ v₀) fun v _ hv =>
      hout v fun hy => hv (Fin.ext (vcell_unique hb h j hy hv₀))]
    exact (hcell v₀).trans (ite_eq_left hv₀).le
  · -- `V_i` lies in none of the vertical intervals
    rw [Finset.sum_eq_zero fun v _ => hout v fun hy => hex ⟨v, hy⟩]
    exact abs_nonneg _

/-! ### The potential -/

/-- Moving one point within a block of `b` horizontal intervals changes `Z` by at most `b/b^h`. -/
theorem abs_Zstep_sub_le {b h j : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (V : Fin n → ℝ) {G G' : Fin n → ℤ} (i : Fin n) (hG : ∀ k, k ≠ i → G' k = G k) {m : ℤ}
    (hm : m ≤ G i ∧ G i < m + b) (hm' : m ≤ G' i ∧ G' i < m + b) :
    |Zstep ε b h j V G' - Zstep ε b h j V G| ≤ (b : ℝ) / (b : ℝ) ^ h := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- the cells of the `c`-th horizontal interval: they change only if `c` is in the block
  have hcol : ∀ c : Fin (b ^ j), ∑ v : Fin (b ^ (h - j)),
      |osc (vcell b h j v) (endpointAvg ε V fun k => sideIdx (G' k) c) -
        osc (vcell b h j v) (endpointAvg ε V fun k => sideIdx (G k) c)| ≤
      if m ≤ ((c : ℕ) : ℤ) ∧ ((c : ℕ) : ℤ) < m + b then 1 else 0 := by
    intro c
    refine (sum_abs_osc_endpointAvg_sub_le hb h j _ ε V i fun k hk => by rw [hG k hk]).trans ?_
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hε i)).trans
      (abs_oldWeight_sideIdx_sub_le hm hm' c)
  -- the sum over all cells, divided by `b^h`
  unfold Zstep
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hbR h), ← Finset.sum_sub_distrib]
  refine div_le_div_of_nonneg_right ?_ (pow_pos hbR h).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun c _ => ?_).trans (sum_ite_block_le (b ^ j) b m))
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hcol c)

/-! ### The next digit -/

/-- The stage-`(j+1)` index of a point is that of one of the `b` children of its interval. -/
lemma refineIdx_mem_block {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) (k : Fin n) :
    (b : ℤ) * g k ≤ refineIdx g r k ∧ refineIdx g r k < (b : ℤ) * g k + b := by
  have hr := (r k).isLt
  unfold refineIdx
  omega

/-- Changing the next digit of the point `i` does not move the other points. -/
lemma refineIdx_update_of_ne {b : ℕ} (g : Fin n → ℤ) (r : Fin n → Fin b) {i k : Fin n}
    (hk : k ≠ i) (a : Fin b) :
    refineIdx g (Function.update r i a) k = refineIdx g r k := by
  unfold refineIdx
  rw [Function.update_of_ne hk]

/-- **Step 1 of the proof of Lemma 2.6**: changing the next digit of the point `i` from
`r i` to `a` changes `Z_{j+1}` by at most `1/M`, where `M = b^{h-1}`. -/
theorem Zstep_update_le {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (V : Fin n → ℝ) (g : Fin n → ℤ) (r : Fin n → Fin b) (i : Fin n)
    (a : Fin b) :
    |Zstep ε b h (j + 1) V (refineIdx g (Function.update r i a)) -
        Zstep ε b h (j + 1) V (refineIdx g r)| ≤ 1 / (b : ℝ) ^ (h - 1) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `b^h = bM`
  have hpow : (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ h)]
  calc |Zstep ε b h (j + 1) V (refineIdx g (Function.update r i a)) -
          Zstep ε b h (j + 1) V (refineIdx g r)|
      ≤ (b : ℝ) / (b : ℝ) ^ h :=
        abs_Zstep_sub_le hb ε hε V i (fun k hk => refineIdx_update_of_ne g r hk a)
          (refineIdx_mem_block g r i) (refineIdx_mem_block g (Function.update r i a) i)
    _ = 1 / (b : ℝ) ^ (h - 1) := by rw [hpow, div_mul_cancel_left₀ hbR.ne', one_div]

end

end R56Audit
end

section
/-!
# Fact A.1 of the manuscript (bounded differences), as stated

Auditor's supplement (not part of the audited archive).

**Fact A.1.** Let `ξ_1, …, ξ_n` be independent random variables, and let `Γ` be a random
element independent of `(ξ_1, …, ξ_n)`. Let `f = φ(Γ, ξ_1, …, ξ_n)` be integrable, where `φ`
is measurable and, for every value `γ` of `Γ`, changing the value of one `ξ_i` changes
`φ(γ, ·)` by at most `c > 0`. Then, for every real `t`, almost surely

`E[exp(t (f - E[f | Γ])) | Γ] ≤ exp(n t² c² / 2)`.

The proof is the one of Appendix A.2: conditioning on `Γ = γ` amounts to fixing the first
argument of `φ` (independence and Fubini); then the variables `ξ_1, …, ξ_n` are revealed one
at a time, and each step costs a factor `cosh(tc) ≤ exp(t²c²/2)`.

`bounded_differences_pi` is the unconditional bound for a product measure, and `fact_A_1` is
the fact as stated; `fact_A_1_integrable` says that the exponential in the statement is
integrable, so that its conditional expectation is the genuine one.

How the proof of the manuscript is carried out here:

* "Since `Γ` is independent of the `ξ_i`, conditioning on `Γ = γ` amounts to fixing the first
  argument of `φ`, by Fubini's theorem": `condExp_comap_eq_integral_of_indepFun` and
  `fact_A_1_freeze`.
* "Any two values of `f` differ by at most `nc`, so `f` is bounded":
  `abs_sub_le_of_bounded_differences`.
* "Martingale differences" and "All differences": for a product measure the conditional
  expectation of `f` given `ξ_1, …, ξ_i` is the integral of `f` over the later coordinates.
  `bounded_differences_pi` integrates the coordinates out one at a time, starting with the
  last one (`integral_pi_snoc`, Fubini), which is the successive conditioning on
  `ξ_1, …, ξ_{n-1}`, then on `ξ_1, …, ξ_{n-2}`, and so on. The martingale differences `Y_i`
  are not introduced as random variables: the function `g'` in the proof is `f_{n-1}`, and
  `g - g'` is `Y_n`.
* "One difference": the manuscript states this step for conditional expectations, "Let `𝓗` be
  a σ-field, and let `E[Y | 𝓗] = 0` and `|Y| ≤ c`", with the conclusion
  `E[e^{tY} | 𝓗] ≤ cosh(tc) ≤ e^{t²c²/2}` for every real `t`.
  - On the route of `fact_A_1`: `exp_mul_le_chord` is the convexity of `y ↦ exp(ty)` on
    `[-c, c]`; `cosh_le_exp_sq_half` is `cosh x ≤ exp(x²/2)`, by comparing the two Taylor
    series term by term with `(2k)! ≥ 2^k k!`; `integral_exp_le_cosh` is the bound
    `E exp(tY) ≤ cosh(tc)` for `E Y = 0`, `|Y| ≤ c`, without conditioning;
    `integral_exp_le_of_centered` continues it to `E exp(tY) ≤ exp(t²c²/2)`; and
    `integral_exp_centered_le` applies it to `Y = f - E f`. The bound is used for the last
    coordinate with the earlier ones fixed, that is, conditionally on `ξ_1, …, ξ_{n-1}`.
  - Restatements, not on the route of `fact_A_1`: `condExp_exp_le_cosh`
    (`E[exp(tY) | 𝓗] ≤ cosh(tc)`) and `condExp_exp_le_exp_sq`
    (`E[exp(tY) | 𝓗] ≤ exp(t²c²/2)`) are the step as the manuscript states it, for a
    sub-σ-field `𝓗` of the σ-field of a probability space. These two theorems are stand-alone
    statements of the manuscript's lemma: the proof of `fact_A_1` in this file works with
    product measures and does not need them.

The random variables `ξ_i` take values in an arbitrary measurable space `E` (the manuscript's
random variables are the case `E = ℝ`; Lemma 2.6 uses `E = {0, …, b-1}`), and `Γ` in an
arbitrary measurable space `G`. This file uses Mathlib only, not the archive.
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Functions of bounded oscillation -/

/-- A real function whose values differ pairwise by at most `d` is bounded. -/
lemma exists_abs_le_of_abs_sub_le {α : Type*} {f : α → ℝ} {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) : ∃ C, ∀ x, |f x| ≤ C := by
  rcases isEmpty_or_nonempty α with h | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun x => (h.false x).elim⟩
  · refine ⟨|f x₀| + d, fun x => ?_⟩
    have h1 := hosc x x₀
    have h2 := abs_sub_abs_le_abs_sub (f x) (f x₀)
    linarith

/-- A measurable function of bounded oscillation is integrable for a finite measure. -/
lemma integrable_of_abs_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) : Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_abs_sub_le hosc
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- For `f` measurable of bounded oscillation, `exp (t (f - m))` is integrable (finite measure). -/
lemma integrable_exp_of_abs_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) (t m : ℝ) :
    Integrable (fun x => Real.exp (t * (f x - m))) μ := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_abs_sub_le hosc
  exact integrable_exp_mul_of_mem_Icc (a := -C - m) (b := C - m) (hf.sub_const m).aemeasurable
    (Filter.Eventually.of_forall fun x =>
      ⟨by linarith [(abs_le.mp (hC x)).1], by linarith [(abs_le.mp (hC x)).2]⟩)

/-- On a probability space, functions that are pointwise `d`-close have `d`-close means. -/
lemma abs_integral_sub_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {u v : α → ℝ} (hu : Integrable u μ) (hv : Integrable v μ) {d : ℝ}
    (h : ∀ a, |u a - v a| ≤ d) : |∫ a, u a ∂μ - ∫ a, v a ∂μ| ≤ d := by
  rw [← integral_sub hu hv]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun a => u a - v a)
    (Filter.Eventually.of_forall h)
  simpa using this

/-- On a probability space, a function of oscillation at most `d` is within `d` of its mean. -/
lemma abs_sub_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {d : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ d) (x : α) : |f x - ∫ y, f y ∂μ| ≤ d := by
  have := abs_integral_sub_integral_le (integrable_const (f x)) hf (hosc x)
  simpa using this

/-! ### One difference -/

/-- `cosh x ≤ exp (x² / 2)`: the Taylor series `cosh x = Σ_k x^{2k} / (2k)!` and
`exp (x² / 2) = Σ_k x^{2k} / (2^k k!)` are compared term by term, using `(2k)! ≥ 2^k k!`. -/
lemma cosh_le_exp_sq_half (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  have hexp : ∀ z : ℝ, HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := fun z => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  -- the series of `cosh x = (exp x + exp (-x)) / 2`; its odd terms vanish
  have h3 : HasSum (fun n : ℕ => (x ^ n / (n.factorial : ℝ) + (-x) ^ n / (n.factorial : ℝ)) / 2)
      (Real.cosh x) := by
    rw [Real.cosh_eq]
    exact ((hexp x).add (hexp (-x))).div_const 2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by
    simpa using h
  have h4 : HasSum (fun k : ℕ => x ^ (2 * k) / ((2 * k).factorial : ℝ)) (Real.cosh x) := by
    have h := (hinj.hasSum_iff
      (f := fun n : ℕ => (x ^ n / (n.factorial : ℝ) + (-x) ^ n / (n.factorial : ℝ)) / 2)
      (a := Real.cosh x) ?_).mpr h3
    · refine h.congr_fun fun k => ?_
      simp only [Function.comp_apply]
      rw [Even.neg_pow (even_two_mul k)]
      ring
    · intro n hn
      have hodd : Odd n := by
        rcases Nat.even_or_odd n with he | ho
        · obtain ⟨m, rfl⟩ := he
          exact absurd ⟨m, by ring⟩ hn
        · exact ho
      rw [Odd.neg_pow hodd]
      ring
  refine hasSum_le (fun k => ?_) h4 (hexp (x ^ 2 / 2))
  -- `x^{2k} / (2k)! ≤ (x²/2)^k / k!`
  rw [div_pow, pow_mul, div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.two_pow_mul_factorial_le_factorial_two_mul k

/-- Convexity of `y ↦ exp (t y)` on `[-c, c]`: the graph lies below the chord. -/
lemma exp_mul_le_chord {c : ℝ} (hc : 0 < c) (t : ℝ) {y : ℝ} (hy : |y| ≤ c) :
    Real.exp (t * y) ≤
      (c + y) / (2 * c) * Real.exp (t * c) + (c - y) / (2 * c) * Real.exp (-(t * c)) := by
  have hy' := abs_le.mp hy
  have ha : 0 ≤ (c + y) / (2 * c) := div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ (c - y) / (2 * c) := div_nonneg (by linarith) (by positivity)
  have hab : (c + y) / (2 * c) + (c - y) / (2 * c) = 1 := by
    field_simp
    ring
  have h := convexOn_exp.2 (Set.mem_univ (t * c)) (Set.mem_univ (-(t * c))) ha hb hab
  simp only [smul_eq_mul] at h
  have he : (c + y) / (2 * c) * (t * c) + (c - y) / (2 * c) * -(t * c) = t * y := by
    field_simp
    ring
  rwa [he] at h

/-- **One difference** (Appendix A.2), without conditioning, the first inequality: if `E Y = 0`
and `|Y| ≤ c`, then `E exp (t Y) ≤ cosh (t c)`. The proof integrates the chord bound
`exp_mul_le_chord`: the chord is affine in `Y`, and `E Y = 0`, so its integral is `cosh (t c)`.

This lemma is on the route of `fact_A_1`; `condExp_exp_le_cosh` is the same bound for
conditional expectations, as the manuscript states it. -/
lemma integral_exp_le_cosh {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0) (t : ℝ) :
    ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.cosh (t * c) := by
  have hYi : Integrable Y μ :=
    Integrable.of_bound hY.aestronglyMeasurable c (Filter.Eventually.of_forall hbd)
  have hi1 : Integrable (fun x => (c + Y x) / (2 * c) * Real.exp (t * c)) μ :=
    (((integrable_const c).add hYi).div_const _).mul_const _
  have hi2 : Integrable (fun x => (c - Y x) / (2 * c) * Real.exp (-(t * c))) μ :=
    (((integrable_const c).sub hYi).div_const _).mul_const _
  -- integrate the chord bound; the integral of the chord is `cosh (t c)`, because `E Y = 0`
  calc ∫ x, Real.exp (t * Y x) ∂μ
      ≤ ∫ x, ((c + Y x) / (2 * c) * Real.exp (t * c) +
          (c - Y x) / (2 * c) * Real.exp (-(t * c))) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
          (hi1.add hi2) (Filter.Eventually.of_forall fun x => exp_mul_le_chord hc t (hbd x))
    _ = Real.cosh (t * c) := by
        rw [integral_add hi1 hi2, integral_mul_const, integral_mul_const, integral_div,
          integral_div, integral_add (integrable_const c) hYi,
          integral_sub (integrable_const c) hYi, hmean, Real.cosh_eq]
        simp only [integral_const, probReal_univ, one_smul, add_zero, sub_zero]
        field_simp

/-- **One difference** (Appendix A.2), without conditioning: if `E Y = 0` and `|Y| ≤ c`, then
`E exp (t Y) ≤ cosh (t c) ≤ exp (t² c² / 2)`. The two inequalities are `integral_exp_le_cosh`
and `cosh_le_exp_sq_half`. -/
lemma integral_exp_le_of_centered {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} (hY : Measurable Y) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ x, |Y x| ≤ c) (hmean : ∫ x, Y x ∂μ = 0) (t : ℝ) :
    ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2) :=
  calc ∫ x, Real.exp (t * Y x) ∂μ ≤ Real.cosh (t * c) := integral_exp_le_cosh hY hc hbd hmean t
    _ ≤ Real.exp ((t * c) ^ 2 / 2) := cosh_le_exp_sq_half _
    _ = Real.exp (t ^ 2 * c ^ 2 / 2) := by rw [mul_pow]

/-- One difference, for a function of oscillation at most `c`:
`E exp(t (f - E f)) ≤ exp(t²c²/2)`. -/
lemma integral_exp_centered_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 ≤ c)
    (hosc : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  have hfi : Integrable f μ := integrable_of_abs_sub_le hf hosc
  have hz : ∫ x, (f x - ∫ y, f y ∂μ) ∂μ = 0 := by
    rw [integral_sub hfi (integrable_const _)]
    simp
  rcases hc.eq_or_lt with rfl | hc'
  · -- `c = 0`: the function is constant
    have h0 : ∀ x, f x - ∫ y, f y ∂μ = 0 := fun x =>
      abs_eq_zero.mp (le_antisymm (abs_sub_integral_le hfi hosc x) (abs_nonneg _))
    simp [h0]
  · -- `Y = f - E f` has mean zero and `|Y| ≤ c`
    exact integral_exp_le_of_centered (hf.sub_const _) hc' (abs_sub_integral_le hfi hosc) hz t

/-! ### One difference, as the manuscript states it

The manuscript states the step for a σ-field `𝓗`: "Let `𝓗` be a σ-field, and let
`E[Y | 𝓗] = 0` and `|Y| ≤ c`." The next two theorems have this form. They are stand-alone
statements of the manuscript's lemma: the proof of `fact_A_1` in this file works with product
measures and does not need them. -/

/-! ### Bounded differences for a product of probability measures -/

/-- A function of `n` coordinates with differences bounded by `c` has oscillation at most `n c`. -/
lemma abs_sub_le_of_bounded_differences {E : Type*} {n : ℕ} (g : (Fin n → E) → ℝ) {c : ℝ}
    (hdiff : ∀ x i a, |g (Function.update x i a) - g x| ≤ c) (x y : Fin n → E) :
    |g x - g y| ≤ n * c := by
  induction n with
  | zero => simp [Subsingleton.elim x y]
  | succ n ih =>
    -- change the first `n` coordinates of `x` into those of `y`, then the last one
    have h1 : |g (Fin.snoc (Fin.init x) (x (Fin.last n))) -
        g (Fin.snoc (Fin.init y) (x (Fin.last n)))| ≤ n * c := by
      refine ih (fun p => g (Fin.snoc p (x (Fin.last n)))) (fun p i a => ?_) _ _
      rw [Fin.snoc_update]
      exact hdiff _ _ _
    have h2 : |g (Fin.snoc (Fin.init y) (y (Fin.last n))) -
        g (Fin.snoc (Fin.init y) (x (Fin.last n)))| ≤ c := by
      have := hdiff (Fin.snoc (Fin.init y) (x (Fin.last n))) (Fin.last n) (y (Fin.last n))
      rwa [Fin.update_snoc_last] at this
    rw [Fin.snoc_init_self] at h1 h2
    have h3 := abs_sub_le (g x) (g (Fin.snoc (Fin.init y) (x (Fin.last n)))) (g y)
    rw [abs_sub_comm (g (Fin.snoc (Fin.init y) (x (Fin.last n)))) (g y)] at h3
    push_cast
    linarith

/-- `Fin.snoc` is jointly measurable. -/
lemma measurable_snoc {E : Type*} [MeasurableSpace E] {n : ℕ} :
    Measurable fun p : (Fin n → E) × E => (Fin.snoc p.1 p.2 : Fin (n + 1) → E) := by
  refine measurable_pi_iff.2 fun j => ?_
  cases j using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

/-- Fubini for the last coordinate of a finite product of probability measures. -/
lemma integral_pi_snoc {E : Type*} [MeasurableSpace E] {n : ℕ}
    (ν : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    {F : (Fin (n + 1) → E) → ℝ} (hF : Integrable F (Measure.pi ν)) :
    ∫ x, F x ∂Measure.pi ν =
      ∫ y, ∫ a, F (Fin.snoc y a) ∂ν (Fin.last n) ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
  have he : ∀ (a : E) (y : Fin n → E),
      (MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).symm (a, y) = Fin.snoc y a :=
    fun a y => Fin.insertNth_last' a y
  have hmp := (measurePreserving_piFinSuccAbove ν (Fin.last n)).symm
  simp only [Fin.succAbove_last] at hmp
  rw [← hmp.integral_comp' F, integral_prod_symm]
  · simp only [he]
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF

/-- **Bounded differences for a product of probability measures** (the unconditional bound in
the proof of Fact A.1): if changing one coordinate changes `g` by at most `c`, then
`E exp(t (g - E g)) ≤ exp(n t² c² / 2)`. -/
theorem bounded_differences_pi {E : Type*} [MeasurableSpace E] {n : ℕ}
    (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (g : (Fin n → E) → ℝ) (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c)
    (hdiff : ∀ x i a, |g (Function.update x i a) - g x| ≤ c) (t : ℝ) :
    ∫ x, Real.exp (t * (g x - ∫ y, g y ∂Measure.pi ν)) ∂Measure.pi ν ≤
      Real.exp (n * t ^ 2 * c ^ 2 / 2) := by
  induction n with
  | zero =>
    -- there is only one point, so `g - E g = 0`
    have hm : ∀ x, g x - ∫ y, g y ∂Measure.pi ν = 0 := fun x => by
      rw [integral_eq_const (Filter.Eventually.of_forall fun y =>
        congrArg g (Subsingleton.elim y x)), sub_self]
    simp [hm]
  | succ n ih =>
    -- `g` as a function of the last coordinate `a`, the first `n` coordinates being `y`
    have hgm : ∀ y : Fin n → E, Measurable fun a => g (Fin.snoc y a) := fun y =>
      hg.comp (measurable_snoc.comp measurable_prodMk_left)
    have hgosc : ∀ (y : Fin n → E) (a b : E), |g (Fin.snoc y a) - g (Fin.snoc y b)| ≤ c := by
      intro y a b
      have := hdiff (Fin.snoc y b) (Fin.last n) a
      rwa [Fin.update_snoc_last] at this
    have hgi : ∀ y : Fin n → E, Integrable (fun a => g (Fin.snoc y a)) (ν (Fin.last n)) :=
      fun y => integrable_of_abs_sub_le (hgm y) (hgosc y)
    -- `g'` is the average of `g` over the last coordinate; it has bounded differences
    let g' : (Fin n → E) → ℝ := fun y => ∫ a, g (Fin.snoc y a) ∂ν (Fin.last n)
    have hg' : Measurable g' :=
      ((hg.comp measurable_snoc).stronglyMeasurable.integral_prod_right').measurable
    have hg'diff : ∀ y i b, |g' (Function.update y i b) - g' y| ≤ c := by
      intro y i b
      refine abs_integral_sub_integral_le (hgi _) (hgi _) fun a => ?_
      rw [Fin.snoc_update]
      exact hdiff _ _ _
    -- `g'` and `g` have the same mean `m`
    have hm : ∫ y, g' y ∂Measure.pi (fun i : Fin n => ν i.castSucc) = ∫ x, g x ∂Measure.pi ν :=
      (integral_pi_snoc ν (integrable_of_abs_sub_le hg
        (abs_sub_le_of_bounded_differences g hdiff))).symm
    -- one difference: the last coordinate, the first `n` coordinates being fixed
    have hlast : ∀ y, ∫ a, Real.exp (t * (g (Fin.snoc y a) - g' y)) ∂ν (Fin.last n) ≤
        Real.exp (t ^ 2 * c ^ 2 / 2) := fun y =>
      integral_exp_centered_le (hgm y) hc (hgosc y) t
    -- all differences: split off the last one, and use the induction hypothesis for `g'`
    set m := ∫ x, g x ∂Measure.pi ν
    calc ∫ x, Real.exp (t * (g x - m)) ∂Measure.pi ν
        = ∫ y, ∫ a, Real.exp (t * (g (Fin.snoc y a) - m)) ∂ν (Fin.last n)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) :=
          integral_pi_snoc ν (integrable_exp_of_abs_sub_le hg
            (abs_sub_le_of_bounded_differences g hdiff) t m)
      _ = ∫ y, Real.exp (t * (g' y - m)) *
            ∫ a, Real.exp (t * (g (Fin.snoc y a) - g' y)) ∂ν (Fin.last n)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
          congr 1 with y
          rw [← integral_const_mul]
          congr 1 with a
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ ∫ y, Real.exp (t * (g' y - m)) * Real.exp (t ^ 2 * c ^ 2 / 2)
            ∂Measure.pi (fun i : Fin n => ν i.castSucc) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => ?_)
            ((integrable_exp_of_abs_sub_le hg'
              (abs_sub_le_of_bounded_differences g' hg'diff) t m).mul_const _)
            (Filter.Eventually.of_forall fun y =>
              mul_le_mul_of_nonneg_left (hlast y) (Real.exp_pos _).le)
          exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun a => (Real.exp_pos _).le)
      _ = (∫ y, Real.exp (t * (g' y - m)) ∂Measure.pi (fun i : Fin n => ν i.castSucc)) *
            Real.exp (t ^ 2 * c ^ 2 / 2) := integral_mul_const _ _
      _ ≤ Real.exp (n * t ^ 2 * c ^ 2 / 2) * Real.exp (t ^ 2 * c ^ 2 / 2) := by
          rw [← hm]
          exact mul_le_mul_of_nonneg_right (ih (fun i : Fin n => ν i.castSucc) g' hg' hg'diff)
            (Real.exp_pos _).le
      _ = Real.exp ((n + 1 : ℕ) * t ^ 2 * c ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-! ### Conditioning on an independent random element -/

/-- **Freezing lemma.** For independent `Γ`, `X`: `E[F(Γ, X) | Γ] = ∫ F(Γ, x) d(law of X)` a.s. -/
lemma condExp_comap_eq_integral_of_indepFun {Ω G H : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] [MeasurableSpace H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Γ : Ω → G} {X : Ω → H} (hΓ : Measurable Γ) (hX : Measurable X) (hindep : IndepFun Γ X μ)
    {F : G × H → ℝ} (hF : Measurable F) (hint : Integrable (fun ω => F (Γ ω, X ω)) μ) :
    μ[fun ω => F (Γ ω, X ω) | MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
      fun ω => ∫ x, F (Γ ω, x) ∂μ.map X := by
  -- the law of `(Γ, X)` is a product measure, and `F` is integrable for it
  have hlaw : μ.map (fun ω => (Γ ω, X ω)) = (μ.map Γ).prod (μ.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hΓ.aemeasurable hX.aemeasurable).mp hindep
  have hFint : Integrable F ((μ.map Γ).prod (μ.map X)) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable (hΓ.prodMk hX).aemeasurable).mpr hint
  let ψ : G → ℝ := fun γ => ∫ x, F (γ, x) ∂μ.map X
  have hψm : Measurable ψ := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hψint : Integrable ψ (μ.map Γ) := hFint.integral_prod_left
  -- `ψ ∘ Γ` has the defining properties of the conditional expectation
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hΓ.comap_le hint (fun s _ _ => ?_)
    (fun s hs _ => ?_) ?_
  · exact (hψint.comp_measurable hΓ).integrableOn
  · obtain ⟨S, hS, rfl⟩ := hs
    calc ∫ ω in Γ ⁻¹' S, ψ (Γ ω) ∂μ = ∫ γ in S, ψ γ ∂μ.map Γ :=
          (setIntegral_map hS hψm.aestronglyMeasurable hΓ.aemeasurable).symm
      _ = ∫ p in S ×ˢ Set.univ, F p ∂(μ.map Γ).prod (μ.map X) := by
          rw [setIntegral_prod _ hFint.integrableOn]
          simp only [Measure.restrict_univ, ψ]
      _ = ∫ p in S ×ˢ Set.univ, F p ∂μ.map (fun ω => (Γ ω, X ω)) := by rw [hlaw]
      _ = ∫ ω in (fun ω => (Γ ω, X ω)) ⁻¹' (S ×ˢ Set.univ), F (Γ ω, X ω) ∂μ :=
          setIntegral_map (hS.prod MeasurableSet.univ) hF.aestronglyMeasurable
            (hΓ.prodMk hX).aemeasurable
      _ = ∫ ω in Γ ⁻¹' S, F (Γ ω, X ω) ∂μ := by
          congr 2
          ext ω
          simp
  · exact (hψm.comp (comap_measurable Γ)).stronglyMeasurable.aestronglyMeasurable

/-- First step of the proof of Fact A.1: the centered exponential is integrable, and
conditioning on `Γ = γ` amounts to fixing the first argument of `φ`. -/
lemma fact_A_1_freeze {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ) {c : ℝ}
    (hdiff : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
        (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω))) μ ∧
      μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
            (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
              MeasurableSpace.comap Γ inferInstance]) ω)) |
          MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
        fun ω => ∫ x, Real.exp (t * (φ (Γ ω, x) -
          ∫ y, φ (Γ ω, y) ∂Measure.pi fun i => μ.map (ξ i))) ∂Measure.pi fun i => μ.map (ξ i) := by
  -- `X = (ξ_1, …, ξ_n)`; its law is the product of the laws of the `ξ_i`
  let X : Ω → (Fin n → E) := fun ω i => ξ i ω
  have hXm : Measurable X := measurable_pi_iff.mpr hξ
  have hlawX : Measure.pi (fun i => μ.map (ξ i)) = μ.map X :=
    ((iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)).mp hξindep).symm
  rw [hlawX]
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXm.aemeasurable
  -- the sections `φ (γ, ·)` have oscillation at most `n c`, and `ψ γ` is their mean
  have hosc : ∀ γ x y, |φ (γ, x) - φ (γ, y)| ≤ n * c := fun γ =>
    abs_sub_le_of_bounded_differences (fun x => φ (γ, x)) (hdiff γ)
  let ψ : G → ℝ := fun γ => ∫ x, φ (γ, x) ∂μ.map X
  have hψm : Measurable ψ := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hcenter : ∀ γ x, |φ (γ, x) - ψ γ| ≤ n * c := fun γ =>
    abs_sub_integral_le (integrable_of_abs_sub_le (hφ.comp measurable_prodMk_left) (hosc γ))
      (hosc γ)
  -- `E[f | Γ] = ψ(Γ)` almost surely
  have hA : μ[fun ω => φ (Γ ω, X ω) | MeasurableSpace.comap Γ inferInstance] =ᵐ[μ]
      fun ω => ψ (Γ ω) :=
    condExp_comap_eq_integral_of_indepFun hΓ hXm hΓindep hφ hint
  -- the centered exponential is a bounded function `F` of the values of `Γ` and `X`
  let F : G × (Fin n → E) → ℝ := fun p => Real.exp (t * (φ p - ψ p.1))
  have hFm : Measurable F :=
    Real.measurable_exp.comp ((hφ.sub (hψm.comp measurable_fst)).const_mul t)
  have hFint : Integrable (fun ω => F (Γ ω, X ω)) μ := by
    refine Integrable.of_bound (hFm.comp (hΓ.prodMk hXm)).aestronglyMeasurable
      (Real.exp (|t| * (n * c))) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * (φ (Γ ω, X ω) - ψ (Γ ω)) ≤ |t * (φ (Γ ω, X ω) - ψ (Γ ω))| := le_abs_self _
      _ = |t| * |φ (Γ ω, X ω) - ψ (Γ ω)| := abs_mul _ _
      _ ≤ |t| * (n * c) := mul_le_mul_of_nonneg_left (hcenter _ _) (abs_nonneg t)
  have hB : (fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
      (μ[fun ω => φ (Γ ω, fun i => ξ i ω) | MeasurableSpace.comap Γ inferInstance]) ω)))
      =ᵐ[μ] fun ω => F (Γ ω, X ω) := by
    filter_upwards [hA] with ω hω
    rw [hω]
  -- freeze `Γ` in `F`
  exact ⟨hFint.congr hB.symm, (condExp_congr_ae hB).trans
    (condExp_comap_eq_integral_of_indepFun hΓ hXm hΓindep hFm hFint)⟩

/-- **Fact A.1 (bounded differences).** Let `ξ_1, …, ξ_n` be independent random variables with
values in a measurable space `E`, and let `Γ` be a random element of a measurable space `G`,
independent of `(ξ_1, …, ξ_n)`. Let `f = φ(Γ, ξ_1, …, ξ_n)` be integrable, where `φ` is
measurable and, for every `γ`, changing one of the last `n` arguments changes `φ(γ, ·)` by at
most `c > 0`. Then for every real `t`, almost surely

`E[exp(t (f - E[f | Γ])) | Γ] ≤ exp(n t² c² / 2)`. -/
theorem fact_A_1 {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (Γ : Ω → G) (ξ : Fin n → Ω → E) (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hΓindep : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : G × (Fin n → E) → ℝ) (hφ : Measurable φ)
    {c : ℝ} (hc : 0 < c)
    (hdiff : ∀ γ x i a, |φ (γ, Function.update x i a) - φ (γ, x)| ≤ c)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (t : ℝ) :
    ∀ᵐ ω ∂μ,
      (μ[fun ω => Real.exp (t * (φ (Γ ω, fun i => ξ i ω) -
            (μ[fun ω => φ (Γ ω, fun i => ξ i ω) |
              MeasurableSpace.comap Γ inferInstance]) ω)) |
          MeasurableSpace.comap Γ inferInstance]) ω ≤
        Real.exp (n * t ^ 2 * c ^ 2 / 2) := by
  -- conditioning on `Γ = γ` fixes the first argument of `φ`; then the unconditional bound
  filter_upwards [(fact_A_1_freeze Γ ξ hΓ hξ hξindep hΓindep φ hφ hdiff hint t).2] with ω hω
  rw [hω]
  haveI : ∀ i, IsProbabilityMeasure (μ.map (ξ i)) := fun i =>
    Measure.isProbabilityMeasure_map (hξ i).aemeasurable
  exact bounded_differences_pi (fun i => μ.map (ξ i)) (fun x => φ (Γ ω, x))
    (hφ.comp measurable_prodMk_left) hc.le (hdiff (Γ ω)) t

end

end R56Audit
end

section
/-!
# Successive conditioning and Markov's inequality (Step 3 of the proof of Lemma 2.6)

Auditor's supplement (not part of the audited archive).

Step 3 of the proof of Lemma 2.6 bounds `E e^{-tT}` for `T = Σ_{j<h} T_j`, and then the
probability that `T ≤ -λ`. It rests on two general facts, which are proved here.

* "So we can condition successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and apply Step 2 each time.
  Multiplying the `h` bounds gives `E e^{-tT} ≤ exp(hnt²/(2M²))`." This is
  `integral_prod_le_of_condExp_le`: let `(ℱ_j)` be a filtration of a probability space, and
  let `W_0, …, W_{h-1}` be random variables with values in `[0, B]` such that `W_j` is
  `ℱ_{j+1}`-measurable and almost surely `E[W_j | ℱ_j] ≤ c_j`, with constants `c_j ≥ 0`;
  then `E[W_0 ⋯ W_{h-1}] ≤ c_0 ⋯ c_{h-1}`. In the manuscript `W_j = e^{-t T_j}`, the bound of
  Step 2 is `c_j = exp(nt²/(2M²))`, and the product of the factors is `e^{-tT}`.
* "By Markov's inequality, `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`". This
  is `measureReal_le_exp_mul_integral_exp_neg`: for `t > 0` and every real `a`,
  `Pr(Z ≤ a) = Pr(e^{-tZ} ≥ e^{-ta}) ≤ e^{ta} E e^{-tZ}`. The manuscript takes `Z = T` and
  `a = -λ`, and then uses the bound for `E e^{-tT}`.

The first fact is proved by induction on `h`. "For every `j`, the earlier terms
`T_0, …, T_{j-1}` are `𝓕_j`-measurable." Accordingly, the product of the first `h` factors is
`ℱ_h`-measurable (`stronglyMeasurable_prod_range`); it lies in `[0, B^h]`
(`prod_range_mem_Icc`), so it is integrable (`integrable_prod_range`). Conditioning on `ℱ_h`
and pulling this product out of the conditional expectation,

`E[W_0 ⋯ W_h] = E[W_0 ⋯ W_{h-1} · E[W_h | ℱ_h]] ≤ c_h · E[W_0 ⋯ W_{h-1}]`.

The factors are not assumed independent, and they need not be at most `c_j` pointwise: only
their conditional expectations are.

This file uses Mathlib only, not the archive.
-/

namespace R56Audit

open MeasureTheory

/-! ### Successive conditioning -/

/-- If each `W_j` is `ℱ_{j+1}`-measurable, then the product of the first `h` factors is
`ℱ_h`-measurable. "For every `j`, the earlier terms `T_0, …, T_{j-1}` are
`𝓕_j`-measurable." -/
lemma stronglyMeasurable_prod_range {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (h : ℕ)
    (hW : ∀ j < h, StronglyMeasurable[ℱ (j + 1)] (W j)) :
    StronglyMeasurable[ℱ h] (fun ω => ∏ j ∈ Finset.range h, W j ω) :=
  Finset.stronglyMeasurable_fun_prod _ fun j hj =>
    StronglyMeasurable.mono (hW j (Finset.mem_range.mp hj))
      (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))

/-- If each factor lies in `[0, B]`, then the product of the first `h` factors lies in
`[0, B^h]`. -/
lemma prod_range_mem_Icc {Ω : Type*} (W : ℕ → Ω → ℝ) (B : ℝ) (h : ℕ)
    (hbound : ∀ j < h, ∀ ω, 0 ≤ W j ω ∧ W j ω ≤ B) (ω : Ω) :
    ∏ j ∈ Finset.range h, W j ω ∈ Set.Icc 0 (B ^ h) := by
  refine ⟨Finset.prod_nonneg fun j hj => (hbound j (Finset.mem_range.mp hj) ω).1, ?_⟩
  calc ∏ j ∈ Finset.range h, W j ω ≤ ∏ _j ∈ Finset.range h, B :=
        Finset.prod_le_prod (fun j hj => (hbound j (Finset.mem_range.mp hj) ω).1)
          fun j hj => (hbound j (Finset.mem_range.mp hj) ω).2
    _ = B ^ h := by rw [Finset.prod_const, Finset.card_range]

/-- For a finite measure, the product of the first `h` factors is integrable: it is measurable
and bounded. -/
lemma integrable_prod_range {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (B : ℝ) (h : ℕ)
    (hW : ∀ j < h, StronglyMeasurable[ℱ (j + 1)] (W j))
    (hbound : ∀ j < h, ∀ ω, 0 ≤ W j ω ∧ W j ω ≤ B) :
    Integrable (fun ω => ∏ j ∈ Finset.range h, W j ω) μ :=
  Integrable.of_mem_Icc 0 (B ^ h)
    (StronglyMeasurable.mono (stronglyMeasurable_prod_range ℱ W h hW)
      (ℱ.le h)).measurable.aemeasurable
    (Filter.Eventually.of_forall (prod_range_mem_Icc W B h hbound))

/-- **Successive conditioning.** Let `(ℱ_j)` be a filtration of a probability space, and let
`W_0, …, W_{h-1}` be random variables with values in `[0, B]` such that `W_j` is
`ℱ_{j+1}`-measurable and almost surely `E[W_j | ℱ_j] ≤ c_j`, with constants `c_j ≥ 0`. Then

`E[W_0 ⋯ W_{h-1}] ≤ c_0 ⋯ c_{h-1}`.

"So we can condition successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and apply Step 2 each time.
Multiplying the `h` bounds gives `E e^{-tT} ≤ exp(hnt²/(2M²))`." The upper bound `B` is used
only to make the products integrable. -/
theorem integral_prod_le_of_condExp_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (c : ℕ → ℝ) (B : ℝ) (h : ℕ)
    (hW : ∀ j < h, StronglyMeasurable[ℱ (j + 1)] (W j))
    (hbound : ∀ j < h, ∀ ω, 0 ≤ W j ω ∧ W j ω ≤ B)
    (hc : ∀ j < h, 0 ≤ c j)
    (hcond : ∀ j < h, ∀ᵐ ω ∂μ, (μ[W j | ℱ j]) ω ≤ c j) :
    ∫ ω, ∏ j ∈ Finset.range h, W j ω ∂μ ≤ ∏ j ∈ Finset.range h, c j := by
  induction h with
  | zero =>
    -- no factors: both sides are `1`
    simp
  | succ h ih =>
    -- the first `h` factors satisfy the hypotheses, so the induction hypothesis applies
    have hW' : ∀ j < h, StronglyMeasurable[ℱ (j + 1)] (W j) := fun j hj =>
      hW j (Nat.lt_succ_of_lt hj)
    have hbound' : ∀ j < h, ∀ ω, 0 ≤ W j ω ∧ W j ω ≤ B := fun j hj =>
      hbound j (Nat.lt_succ_of_lt hj)
    have hind := ih hW' hbound' (fun j hj => hc j (Nat.lt_succ_of_lt hj))
      fun j hj => hcond j (Nat.lt_succ_of_lt hj)
    -- the product of the earlier factors, the last factor and their product are integrable
    have hP : Integrable (fun ω => ∏ j ∈ Finset.range h, W j ω) μ :=
      integrable_prod_range ℱ W B h hW' hbound'
    have hWh : Integrable (W h) μ := Integrable.of_mem_Icc 0 B
      (StronglyMeasurable.mono (hW h (Nat.lt_succ_self h))
        (ℱ.le (h + 1))).measurable.aemeasurable
      (Filter.Eventually.of_forall (hbound h (Nat.lt_succ_self h)))
    have hsucc : (fun ω => ∏ j ∈ Finset.range (h + 1), W j ω) =
        (fun ω => ∏ j ∈ Finset.range h, W j ω) * W h :=
      funext fun ω => Finset.prod_range_succ (fun j => W j ω) h
    have hprod : Integrable ((fun ω => ∏ j ∈ Finset.range h, W j ω) * W h) μ := by
      rw [← hsucc]
      exact integrable_prod_range ℱ W B (h + 1) hW hbound
    -- the product of the earlier factors is `ℱ_h`-measurable: pull it out of `E[· | ℱ_h]`
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_prod_range ℱ W h hW') hprod hWh
    have hright : Integrable (fun ω => (∏ j ∈ Finset.range h, W j ω) * (μ[W h | ℱ h]) ω) μ :=
      integrable_condExp.congr hpull
    calc ∫ ω, ∏ j ∈ Finset.range (h + 1), W j ω ∂μ
        = ∫ ω, (μ[(fun ω => ∏ j ∈ Finset.range h, W j ω) * W h | ℱ h]) ω ∂μ := by
          -- condition on `ℱ_h`
          rw [integral_condExp (ℱ.le h), hsucc]
      _ = ∫ ω, (∏ j ∈ Finset.range h, W j ω) * (μ[W h | ℱ h]) ω ∂μ := integral_congr_ae hpull
      _ ≤ ∫ ω, (∏ j ∈ Finset.range h, W j ω) * c h ∂μ := by
          -- the bound for the last factor; the product of the earlier factors is nonnegative
          refine integral_mono_ae hright (hP.mul_const (c h)) ?_
          filter_upwards [hcond h (Nat.lt_succ_self h)] with ω hω
          exact mul_le_mul_of_nonneg_left hω (prod_range_mem_Icc W B h hbound' ω).1
      _ = (∫ ω, ∏ j ∈ Finset.range h, W j ω ∂μ) * c h := integral_mul_const (c h) _
      _ ≤ (∏ j ∈ Finset.range h, c j) * c h :=
          -- the bounds for the earlier factors
          mul_le_mul_of_nonneg_right hind (hc h (Nat.lt_succ_self h))
      _ = ∏ j ∈ Finset.range (h + 1), c j := (Finset.prod_range_succ c h).symm

/-! ### Markov's inequality -/

/-- **Markov's inequality for `e^{-tZ}`.** If `t > 0` and `e^{-tZ}` is integrable, then for
every real `a`,

`Pr(Z ≤ a) = Pr(e^{-tZ} ≥ e^{-ta}) ≤ e^{ta} E e^{-tZ}`.

"By Markov's inequality, `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`": this
is the case `Z = T`, `a = -λ`, followed by the bound for `E e^{-tT}`. The measure need not be
finite, and neither `Z` nor the event is assumed measurable. -/
theorem measureReal_le_exp_mul_integral_exp_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (Z : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => Real.exp (-t * Z ω)) μ) (a : ℝ) :
    μ.real {ω | Z ω ≤ a} ≤ Real.exp (t * a) * ∫ ω, Real.exp (-t * Z ω) ∂μ := by
  -- `Z ≤ a` if and only if `e^{-tZ} ≥ e^{-ta}`, since `t > 0`
  have hevent : {ω | Z ω ≤ a} = {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} := by
    ext ω
    change Z ω ≤ a ↔ Real.exp (-t * a) ≤ Real.exp (-t * Z ω)
    rw [Real.exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff, mul_le_mul_iff_right₀ ht]
  calc μ.real {ω | Z ω ≤ a}
      = μ.real {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} := by rw [hevent]
    _ ≤ (∫ ω, Real.exp (-t * Z ω) ∂μ) / Real.exp (-t * a) :=
        -- Markov's inequality for the nonnegative function `e^{-tZ}` at the level `e^{-ta}`
        (le_div_iff₀' (Real.exp_pos _)).mpr (mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos (-t * Z ω)).le) hint _)
    _ = Real.exp (t * a) * ∫ ω, Real.exp (-t * Z ω) ∂μ := by
        rw [neg_mul, Real.exp_neg, div_inv_eq_mul, mul_comm]

end R56Audit
end

section
/-!
# Lemma 2.6 of the manuscript (fluctuations)

Auditor's supplement (not part of the audited archive).

**Lemma 2.6.** Fix a coloring, and let `T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` be the
fluctuation term of (10). Then, for every `λ > 0`,

`Pr(T ≤ -λ) ≤ exp(-λ² M² / (2hn))`.

Here `Z_j` is the potential `Zpot` of display (1), `𝓕_j` is `stageSigma n b j`, and `T` is
`fluct χ b h` of `ConditionalGain.lean`. (The statement for the manuscript's `𝓕_j`, the σ-field
`digitSigma n b j` of the heights and the first `j` digits, is `lemma_2_6_digits` in
`Digits.lean`; it follows from `lemma_2_6`.) The proof has the three steps of the manuscript:

* Step 1, one digit: `Zstep_update_le` (`Influence.lean`);
* Step 2, one transition: `condExp_exp_step`, by **Fact A.1** (`fact_A_1`) with `Γ` the
  heights and the stage-`j` indices, `ξ_1, …, ξ_n` the next digits and `c = 1/M`; the next
  digits are independent of each other and of `𝓕_j` (`iIndepFun_fresh`,
  `indepFun_coarse_fresh`);
* Step 3, all transitions: the earlier terms are `𝓕_j`-measurable
  (`fluctTerm_measurable_of_lt`); `integral_exp_neg_sum_le`, conditioning successively
  (`integral_prod_le_of_condExp_le`, for the factors `e^{-t T_j}` and the bounds
  `exp(n t² / (2M²))` of Step 2); and Markov's inequality
  (`measureReal_le_exp_mul_integral_exp_neg`) with `t = λM²/(hn)`. The two general facts,
  successive conditioning and Markov's inequality, are proved from Mathlib in
  `SuccessiveConditioning.lean`.

`condExp_exp_step` and `integral_exp_neg_sum_le` read `Z_{j+1}` from the heights and the
indices (`Zproc`) and write `E[Z_{j+1} | 𝓕_j]` as the average over the next digits (`Zmean`);
almost surely this changes nothing (`fluctTerm_ae_eq`, `fluct_ae_eq`). The displays of the two
steps are then stated in the manuscript's terms, with the potential `Zpot`, Mathlib's
conditional expectation given `𝓕_j` and the fluctuation term `fluct`:

* `lemma_2_6_step2`: with `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]`, almost surely
  `E[e^{-t T_j} | 𝓕_j] ≤ exp(n t² / (2M²))`;
* `lemma_2_6_step3`: `E e^{-tT} ≤ exp(h n t² / (2M²))`;
* `integrable_exp_neg_fluctTerm`, `integrable_exp_neg_fluct`: `e^{-t T_j}` and `e^{-tT}` are
  integrable, so the conditional expectation and the expectation of these two displays are
  those of integrable functions;
* `lemma_2_6_markov`: `Pr(T ≤ -λ) ≤ exp(-tλ + h n t² / (2M²))` for every `t > 0`, by Step 3
  and Markov's inequality;
* `lemma_2_6`: Lemma 2.6, by the choice `t = λM²/(hn)`.
-/

namespace R56Audit

open MeasureTheory ProbabilityTheory Finset Riesz Riesz.PointSets Oscillation

noncomputable section

variable {n : ℕ}

/-! ### Step 2: one transition -/

/-- `Z_{j+1}` as a function `φ(Γ, ξ)` of the `𝓕_j`-measurable data `Γ` (the heights and the
stage-`j` indices) and of the next digits `ξ`. -/
def nextPot (ε : Fin n → ℝ) (b h j : ℕ)
    (p : ((Fin n → ℝ) × (Fin n → ℤ)) × (Fin n → Fin b)) : ℝ :=
  Zstep ε b h (j + 1) p.1.1 (refineIdx p.1.2 p.2)

lemma measurable_nextPot {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h j : ℕ) :
    Measurable (nextPot ε b h j) :=
  measurable_from_prod_countable_left fun r => measurable_Zstep_refine hb ε h (j + 1) r

/-- **Step 2 of the proof of Lemma 2.6**: for every real `t`, almost surely
`E[exp(t (Z_{j+1} - E[Z_{j+1} | 𝓕_j])) | 𝓕_j] ≤ exp(n t² / (2M²))`. This is Fact A.1 with
`c = 1/M`. Here `E[Z_{j+1} | 𝓕_j]` is written as the average over the next digits. -/
theorem condExp_exp_step {b h j : ℕ} (hb : 0 < b) (hj : j < h) (ε : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (t : ℝ) :
    ∀ᵐ P ∂pointSampleLaw n,
      ((pointSampleLaw n)[fun P => Real.exp (t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)) |
          stageSigma n b j]) P ≤
        Real.exp (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `Z_{j+1} = φ(Γ, ξ)`
  have hf : ∀ P : Fin n → ℝ × ℝ, nextPot ε b h j (coarseInfo n (b ^ j) P,
      fun i => freshGridIndex (b ^ j) b hb (P i).1) = Zproc ε b h (j + 1) P :=
    fun P => (Zproc_succ hb hj ε P).symm
  have hA := fact_A_1 (μ := pointSampleLaw n) (coarseInfo n (b ^ j))
    (fun (i : Fin n) (P : Fin n → ℝ × ℝ) => freshGridIndex (b ^ j) b hb (P i).1)
    (measurable_coarseInfo n (b ^ j))
    (fun i => (measurable_freshGridIndex (b ^ j) b hb).comp
      (measurable_fst.comp (measurable_pi_apply i)))
    (iIndepFun_fresh n (b ^ j) b hb)
    (indepFun_coarse_fresh n (b ^ j) b (pow_pos hb j) hb)
    (nextPot ε b h j) (measurable_nextPot hb ε h j)
    (c := 1 / (b : ℝ) ^ (h - 1)) (by positivity)
    (fun γ x i a => Zstep_update_le hb hj ε hε γ.1 γ.2 x i a)
    (by simp only [hf]; exact integrable_Zproc hb ε hε h (j + 1)) t
  simp only [hf] at hA
  -- replace `E[Z_{j+1} | 𝓕_j]` by the average over the next digits
  have hcongr : (fun P => Real.exp (t * (Zproc ε b h (j + 1) P -
      ((pointSampleLaw n)[Zproc ε b h (j + 1) | stageSigma n b j]) P))) =ᵐ[pointSampleLaw n]
      fun P => Real.exp (t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)) := by
    filter_upwards [condExp_Zproc_succ hb hj ε hε] with P hP
    rw [hP]
  filter_upwards [hA, condExp_congr_ae (m := stageSigma n b j) hcongr] with P hP hP'
  rw [← hP']
  exact hP

/-! ### Step 3: all transitions -/

/-- The sum of the centered increments, with the conditional expectations written as averages
over the next digits. Almost surely this is the fluctuation term `T` (`fluct_ae_eq`). -/
def fluctStep (ε : Fin n → ℝ) (b h : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range h, (Zproc ε b h (j + 1) P - Zmean ε b h j P)

lemma measurable_fluctStep {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h : ℕ) :
    Measurable (fluctStep ε b h) :=
  Finset.measurable_sum _ fun j _ => (measurable_Zproc hb ε h (j + 1)).sub
    (measurable_Zmean hb ε h j)

lemma abs_fluctStep_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) (h : ℕ)
    (P : Fin n → ℝ × ℝ) : |fluctStep ε b h P| ≤ h * n := by
  unfold fluctStep
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range h, |Zproc ε b h (j + 1) P - Zmean ε b h j P|
      ≤ ∑ _j ∈ Finset.range h, (n : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have h1 := Zproc_nonneg hb ε h (j + 1) P
        have h2 := Zproc_le hb ε hε h (j + 1) P
        have h3 := Zmean_nonneg hb ε h j P
        have h4 := Zmean_le hb (Finset.mem_range.mp hj) ε hε P
        rw [abs_le]
        constructor <;> linarith
    _ = h * n := by simp

/-- "For every `j`, the earlier terms `T_0, …, T_{j-1}` are `𝓕_j`-measurable." Here `𝓕_j` is
the σ-field `stageSigma n b j`, and the term `T_k = Z_{k+1} - E[Z_{k+1} | 𝓕_k]` is written
with `Z_{k+1}` read from the heights and the interval indices (`Zproc`) and with the average
over the next digits (`Zmean`) in place of the conditional expectation (`fluctTerm_ae_eq`). -/
lemma fluctTerm_measurable_of_lt {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (h : ℕ) {k j : ℕ}
    (hkj : k < j) :
    Measurable[stageSigma n b j] (fun P => Zproc ε b h (k + 1) P - Zmean ε b h k P) := by
  -- `Z_{k+1}` is `𝓕_{k+1}`-measurable, and its average over the next digits is `𝓕_k`-measurable
  have h1 : Measurable[stageSigma n b j] (Zproc ε b h (k + 1)) :=
    ((Zproc_stronglyMeasurable hb ε h (k + 1)).mono (stageSigma_mono hb n hkj)).measurable
  have h2 : Measurable[stageSigma n b j] (Zmean ε b h k) :=
    ((Zmean_stronglyMeasurable hb ε h k).mono (stageSigma_mono hb n hkj.le)).measurable
  exact h1.sub h2

/-- **Step 3 of the proof of Lemma 2.6**: `E exp(-tT) ≤ exp(h n t² / (2M²))`, for every real
`t`. Here the conditional expectations in `T` are written as averages over the next digits
(`fluctStep`). "So we can condition successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and apply
Step 2 each time. Multiplying the `h` bounds gives `E e^{-tT} ≤ exp(hnt²/(2M²))`." The
successive conditioning is `integral_prod_le_of_condExp_le`, for the factors `e^{-t T_j}`. -/
theorem integral_exp_neg_sum_le {b : ℕ} (hb : 0 < b) (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (h : ℕ) (t : ℝ) :
    ∫ P, Real.exp (-t * fluctStep ε b h P) ∂pointSampleLaw n ≤
      Real.exp (h * (n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2)) := by
  set c0 : ℝ := n * t ^ 2 * (1 / (b : ℝ) ^ (h - 1)) ^ 2 / 2 with hc0
  -- the factors: `W_j = e^{-t T_j}`, with `T_j = Z_{j+1} - E[Z_{j+1} | 𝓕_j]`
  let W : ℕ → (Fin n → ℝ × ℝ) → ℝ := fun j P =>
    Real.exp (-t * (Zproc ε b h (j + 1) P - Zmean ε b h j P))
  -- `W_j` is `𝓕_{j+1}`-measurable
  have hW : ∀ j < h, StronglyMeasurable[stageFiltration n b hb (j + 1)] (W j) := fun j _ =>
    (((fluctTerm_measurable_of_lt hb ε h (Nat.lt_succ_self j)).const_mul
      (-t)).exp).stronglyMeasurable
  -- `0 ≤ W_j ≤ e^{|t| n}`, since `|T_j| ≤ n`
  have hbound : ∀ j < h, ∀ P, 0 ≤ W j P ∧ W j P ≤ Real.exp (|t| * n) := by
    intro j hj P
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have h1 := Zproc_nonneg hb ε h (j + 1) P
    have h2 := Zproc_le hb ε hε h (j + 1) P
    have h3 := Zmean_nonneg hb ε h j P
    have h4 := Zmean_le hb hj ε hε P
    have h5 : |Zproc ε b h (j + 1) P - Zmean ε b h j P| ≤ n := by
      rw [abs_le]
      constructor <;> linarith
    calc -t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)
        ≤ |-t * (Zproc ε b h (j + 1) P - Zmean ε b h j P)| := le_abs_self _
      _ = |t| * |Zproc ε b h (j + 1) P - Zmean ε b h j P| := by rw [abs_mul, abs_neg]
      _ ≤ |t| * n := mul_le_mul_of_nonneg_left h5 (abs_nonneg t)
  -- Step 2 for each factor, with `-t` in place of `t`: `E[W_j | 𝓕_j] ≤ exp(n t² / (2M²))`
  have hcond : ∀ j < h, ∀ᵐ P ∂pointSampleLaw n,
      ((pointSampleLaw n)[W j | stageFiltration n b hb j]) P ≤ Real.exp c0 := by
    intro j hj
    have hstep := condExp_exp_step hb hj ε hε (-t)
    rw [neg_sq, ← hc0] at hstep
    exact hstep
  -- the product of the factors is `e^{-tT}`
  have he : ∀ P, Real.exp (-t * fluctStep ε b h P) = ∏ j ∈ Finset.range h, W j P := by
    intro P
    unfold fluctStep
    rw [Finset.mul_sum, Real.exp_sum]
  calc ∫ P, Real.exp (-t * fluctStep ε b h P) ∂pointSampleLaw n
      = ∫ P, ∏ j ∈ Finset.range h, W j P ∂pointSampleLaw n :=
        integral_congr_ae (Filter.Eventually.of_forall he)
    _ ≤ ∏ _j ∈ Finset.range h, Real.exp c0 :=
        -- conditioning successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0`, with Step 2 each time
        integral_prod_le_of_condExp_le (stageFiltration n b hb) W (fun _ => Real.exp c0)
          (Real.exp (|t| * n)) h hW hbound (fun _ _ => (Real.exp_pos c0).le) hcond
    _ = Real.exp (h * c0) := by
        -- multiplying the `h` bounds
        rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]

/-! ### The displays of Steps 2 and 3 in the manuscript's terms -/

/-- Almost surely, the fluctuation term `T` of display (10) is the sum of the centered
increments with the conditional expectations written as averages over the next digits. -/
lemma fluct_ae_eq {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) :
    fluct χ b h =ᵐ[pointSampleLaw n] fluctStep (sgn χ) b h := by
  have hall : ∀ᵐ P ∂pointSampleLaw n, ∀ j ∈ Finset.range h,
      Zpot χ b h (j + 1) P - ((pointSampleLaw n)[Zpot χ b h (j + 1) | stageSigma n b j]) P =
        Zproc (sgn χ) b h (j + 1) P - Zmean (sgn χ) b h j P := by
    refine (ae_ball_iff (Finset.range h).countable_toSet).mpr fun j hj => ?_
    have hj' : j < h := Finset.mem_range.mp hj
    filter_upwards [Zpot_ae_eq_Zproc hb (by omega : j + 1 ≤ h) χ,
      condExp_Zpot_succ hb hj' χ] with P h1 h2
    rw [h1, h2]
  unfold fluct fluctStep
  rw [← pointSampleLaw_eq_unifPts]
  filter_upwards [hall] with P hP
  exact Finset.sum_congr rfl hP

/-- For a finite measure, `e^{-tX}` is integrable if `X` is almost everywhere equal to a
measurable function `Y` with `|Y| ≤ B`. -/
lemma integrable_exp_neg_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hXY : X =ᵐ[μ] Y) (hY : Measurable Y) {B : ℝ}
    (hB : ∀ ω, |Y ω| ≤ B) (t : ℝ) :
    Integrable (fun ω => Real.exp (-t * X ω)) μ := by
  -- `Y` is measurable with values in `[-B, B]`, so `e^{-tY}` is measurable and bounded
  have hint : Integrable (fun ω => Real.exp (-t * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc hY.aemeasurable
      (Filter.Eventually.of_forall fun ω => abs_le.mp (hB ω))
  refine hint.congr ?_
  filter_upwards [hXY] with ω hω
  rw [hω]

/-- `e^{-tT}` is integrable: almost surely, `T` is a measurable function with `|T| ≤ hn`. So
the expectation in `lemma_2_6_step3` is that of an integrable function. -/
lemma integrable_exp_neg_fluct {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (t : ℝ) :
    Integrable (fun P => Real.exp (-t * fluct χ b h P)) (unifPts n) := by
  have hT := fluct_ae_eq hb h χ
  rw [pointSampleLaw_eq_unifPts] at hT
  exact integrable_exp_neg_of_ae_eq hT (measurable_fluctStep hb (sgn χ) h)
    (abs_fluctStep_le hb (sgn χ) (fun i => (abs_sgn χ i).le) h) t

/-- **Step 3 of the proof of Lemma 2.6**, as displayed: `E e^{-tT} ≤ exp(h n t² / (2M²))`. -/
theorem lemma_2_6_step3 {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (t : ℝ) :
    ∫ P, Real.exp (-t * fluct χ b h P) ∂unifPts n ≤
      Real.exp (h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
  have hε : ∀ i, |sgn χ i| ≤ 1 := fun i => (abs_sgn χ i).le
  rw [← pointSampleLaw_eq_unifPts]
  -- almost surely, `T` is the sum of the centered increments of `integral_exp_neg_sum_le`
  have hcongr : (fun P => Real.exp (-t * fluct χ b h P)) =ᵐ[pointSampleLaw n]
      fun P => Real.exp (-t * fluctStep (sgn χ) b h P) := by
    filter_upwards [fluct_ae_eq hb h χ] with P hP
    rw [hP]
  rw [integral_congr_ae hcongr]
  -- conditioning successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and applying Step 2 each time
  refine (integral_exp_neg_sum_le hb (sgn χ) hε h t).trans_eq ?_
  congr 1
  ring

/-! ### Lemma 2.6 -/

/-- **Markov's inequality in Step 3 of the proof of Lemma 2.6**: for every `t > 0`,
`Pr(T ≤ -λ) ≤ exp(-tλ + h n t² / (2M²))`. "By Markov's inequality,
`Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`". -/
theorem lemma_2_6_markov {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (lam : ℝ) {t : ℝ}
    (ht : 0 < t) :
    (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
      Real.exp (-t * lam + h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
  calc (unifPts n).real {P | fluct χ b h P ≤ -lam}
      ≤ Real.exp (t * -lam) * ∫ P, Real.exp (-t * fluct χ b h P) ∂unifPts n :=
        -- Markov's inequality: `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ e^{-tλ} E e^{-tT}`
        measureReal_le_exp_mul_integral_exp_neg (fluct χ b h) ht
          (integrable_exp_neg_fluct hb h χ t) (-lam)
    _ ≤ Real.exp (t * -lam) * Real.exp (h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) :=
        -- Step 3: `E e^{-tT} ≤ exp(h n t² / (2M²))`
        mul_le_mul_of_nonneg_left (lemma_2_6_step3 hb h χ t) (Real.exp_pos _).le
    _ = Real.exp (-t * lam + h * n * t ^ 2 / (2 * ((b : ℝ) ^ (h - 1)) ^ 2)) := by
        rw [← Real.exp_add, mul_neg, ← neg_mul]

/-- **Lemma 2.6 (fluctuations).** Fix a coloring, and let
`T = Σ_{j<h} (Z_{j+1} - E[Z_{j+1} | 𝓕_j])` be the fluctuation term of (10). Then, for every
`λ > 0`,

`Pr(T ≤ -λ) ≤ exp(-λ² M² / (2hn))`,   `M = b^{h-1}`. -/
theorem lemma_2_6 {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) {lam : ℝ} (hlam : 0 < lam) :
    (unifPts n).real {P | fluct χ b h P ≤ -lam} ≤
      Real.exp (-(lam ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n))) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- if there are no transitions or no points, the bound is `1`
  by_cases hdeg : h = 0 ∨ n = 0
  · have : (2 : ℝ) * h * n = 0 := by
      rcases hdeg with rfl | rfl <;> simp
    rw [this, div_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => hdeg (Or.inl h0)
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hdeg (Or.inr h0)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  -- Step 3 and Markov's inequality (`lemma_2_6_markov`), for `t = λM²/(hn)`:
  -- `Pr(T ≤ -λ) ≤ exp(-tλ + hnt²/(2M²))`
  set t : ℝ := lam * ((b : ℝ) ^ (h - 1)) ^ 2 / (h * n) with ht
  have htpos : 0 < t := by positivity
  refine (lemma_2_6_markov hb h χ lam htpos).trans_eq ?_
  -- "the choice `t = λM²/(hn)` gives the claim": the exponent is `-λ²M²/(2hn)`
  congr 1
  rw [ht]
  field_simp
  ring

end

end R56Audit
end

section
/-!
# Lemma 2.5(ii) of the manuscript (good transitions), by the proof of the manuscript

Auditor's supplement (not part of the audited archive).

**Lemma 2.5(ii).** If `M ≤ n`, then `Pr(G_j^c) ≤ (48/b)^{n/2}`, and hence
`Pr(G^c) ≤ h (48/b)^{n/2}`.

`lemma_2_5_ii` and `lemma_2_5_ii_all` are these two bounds, proved by the proof in
Section 2.4 of the manuscript. The archive's probability estimate and its cell labels are not
used (`GoodTransitionsArchive.lean` shows that they give the same bounds). The regions, the
numbers `m_R`, "heavy", the events `G_j`, and the almost sure events `InUnit` (all coordinates
in `(0,1]`) and `NoGrid` (no coordinate of the form `k/b^r`) are those of
`GoodTransitions.lean`; the old vertical intervals are `vcell` of `Potential.lean`; the law of
the points is `unifPts`.

Throughout, `M = b^{h-1}`, and the comparison rectangles of the transition `j → j+1` are
indexed by the pairs `(c, v)`, `c < b^j`, `v < b^{h-j-1}`.

| Manuscript | Here |
| --- | --- |
| boundary strip: "the bottom or the top old cell" | `bottomStrip`, `topStrip` |
| the union of the boundary strips | `boundaryStrips b h j` |
| a collection `𝒮` of inner regions | `𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))` |
| "fewer than `M/b`" regions | `(𝒮.card : ℝ) < b ^ (h - 1) / b`, `smallCollections` |
| `W_𝒮`: "the union of the boundary strips and of the regions in `𝒮`" | `Wset b h j 𝒮` |
| the collection of the heavy regions | `heavySet b h j P` |
| "the union `W` of the boundary strips and the heavy regions" | `Wset b h j (heavySet b h j P)` |
| `E_𝒮`: "the event that at least `n/2` points lie in `W_𝒮`" | `crowdEvent b h j 𝒮` |

The steps of the proof of the manuscript, with its sentences. (The manuscript proves step 3
before step 2, and the first half of step 6 before step 4.)

1. *The boundary strips and `W_𝒮`.* `bottomStrip_eq`, `topStrip_eq`,
   `prod_vcell_subset_innerRegion`: of the `b` old cells of a comparison rectangle, the
   bottom and the top one are its boundary strips, and the others lie in its inner region.
2. `innerRegion_inj`, `sum_innerCount_le`, `card_heavySet_lt`: "There are fewer than `M/b`
   heavy regions, since no point lies in two inner regions and each heavy one contains more
   than `bn/M` of the `n` points."
3. `mem_boundaryStrips_or_innerRegion`, `mem_Wset_heavySet`, `half_lt_card_Wset`: "Suppose
   that `G_j` fails, that is, fewer than `n/2` points lie in inner regions that are not
   heavy. Every other point lies in a heavy inner region or in a boundary strip \[…\]. So
   more than `n/2` points lie in the union `W` of the boundary strips and the heavy regions."
4. `volume_boundaryStrips`, `volume_innerRegion_lt`, `volume_innerRegions_lt`,
   `volume_Wset_le`, `unitSq_Wset_le`: "The boundary strips are two of the `b` old cells of
   every comparison rectangle, so they cover an area of `2/b`. The regions in `𝒮` have area
   less than `1/M` each, so they cover an area of less than `1/b`. Hence `W_𝒮` is a fixed set
   of area at most `3/b`." The first sentence is the equality `volume_boundaryStrips`, for
   `b ≥ 2`: the union of the boundary strips is the product of `[0,1]` and of the union of
   `2 b^{h-j-1}` disjoint vertical intervals of length `b^{j-h}` (`boundaryStrips_eq_prod`).
   The second sentence is `volume_innerRegion_lt` and the strict inequality
   `volume_innerRegions_lt`. The third sentence is `volume_Wset_le`; for the boundary strips
   it uses the upper bound `volume_boundaryStrips_le`, which holds for every `b ≥ 1` (for
   `b = 1` the two boundary strips of a comparison rectangle coincide).
   `volume_innerRegions_le` is the weak form of `volume_innerRegions_lt`.
5. `exists_card_eq_ceil_half`, `unifPts_forall_mem`, `unifPts_forall_mem_le`,
   `unifPts_half_mem_le`, `unifPts_crowdEvent_le`: "If `E_𝒮` occurs, then there is a set of
   `⌈n/2⌉` indices whose points all lie in `W_𝒮`. There are at most `2^n` sets of indices.
   The `n` points are independent and uniform in the unit square, so the points of a given
   set all lie in the fixed set `W_𝒮` with probability at most
   `(3/b)^{⌈n/2⌉} ≤ (3/b)^{n/2}`, since `3/b ≤ 1`. So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`."
6. `mem_crowdEvent_heavySet`, `bad_subset_iUnion_crowdEvent`, `bad_ae_le_iUnion_crowdEvent`,
   `card_smallCollections_le`, `unifPts_bad_le`, `two_pow_mul_rpow_le`: "if `G_j` fails, then
   `E_𝒮` occurs for the collection `𝒮` of heavy regions. So `G_j^c` is contained in the union
   of the events `E_𝒮`. \[…\] There are at most `2^M` collections of inner regions, so
   `Pr(G_j^c) ≤ 2^{M+n} (3/b)^{n/2}`. Since `M ≤ n`, we have `2^{M+n} ≤ 4^n = 16^{n/2}`, which
   gives `(48/b)^{n/2}`. A union bound over the `h` transitions gives the bound on
   `Pr(G^c)`."

**Where the probability-one event of Section 2.1 enters.** Steps 1, 4 and 5 do not need it.
Step 2 uses that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`): the
horizontal intervals are closed, so two neighbouring inner regions share a vertical segment.
Step 3 uses that the points lie in `[0,1] × [0,1)`: a point of height `1` lies in no
comparison rectangle. On `InUnit` and `NoGrid` all coordinates lie in `(0,1)`
(`mem_unit_of_inUnit_of_noGrid`). So in step 6 the event `G_j^c` is contained in the union of
the events `E_𝒮` on these two events, which have probability one (`ae_inUnit`, `ae_noGrid`).

No set needs to be measurable for Lemma 2.5(ii): its proof uses only that a measure is
monotone and subadditive, and the product formula for boxes (`Measure.prod_prod`,
`Measure.pi_pi`). The equality `volume_boundaryStrips`, which the proof of the lemma does not
use, needs in addition that the length is additive on disjoint intervals (`measure_iUnion`,
`measure_union`).
-/

namespace R56Audit

open MeasureTheory Finset Riesz Riesz.PointSets Oscillation

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### 1. The boundary strips and the set `W_𝒮` -/

/-- The bottom old cell of the comparison rectangle `R = I × J` with indices `(c, v)` of the
transition `j → j+1`, where `I = [c b^{-j}, (c+1) b^{-j}]` and
`J = [v b^{j+1-h}, (v+1) b^{j+1-h})`: the points of `R` whose height lies in the bottom block
`[v b^{j+1-h}, v b^{j+1-h} + b^{j-h})` of `J`. -/
def bottomStrip (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico ((v : ℝ) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h)
      (((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h)

/-- The top old cell of the comparison rectangle `R = I × J` with indices `(c, v)` of the
transition `j → j+1`: the points of `R` whose height lies in the top block
`[(v+1) b^{j+1-h} - b^{j-h}, (v+1) b^{j+1-h})` of `J`. -/
def topStrip (b h j c v : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
    Set.Ico ((((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h)
      (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) / (b : ℝ) ^ h)

/-- The union of the boundary strips of the transition `j → j+1`. A boundary strip is "the
bottom or the top old cell of a comparison rectangle". -/
def boundaryStrips (b h j : ℕ) : Set (ℝ × ℝ) :=
  ⋃ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)),
    bottomStrip b h j p.1 p.2 ∪ topStrip b h j p.1 p.2

/-- `W_𝒮`: "the union of the boundary strips and of the regions in `𝒮`", for a collection `𝒮`
of inner regions. -/
def Wset (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) : Set (ℝ × ℝ) :=
  boundaryStrips b h j ∪ ⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2

/-- The collection of the heavy inner regions. With it, `Wset b h j (heavySet b h j P)` is
"the union `W` of the boundary strips and the heavy regions". -/
def heavySet (b h j : ℕ) (P : Fin n → ℝ × ℝ) : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))) :=
  Finset.univ.filter (fun p => Heavy b h j P p.1 p.2)

/-- `E_𝒮`: "the event that at least `n/2` points lie in `W_𝒮`". -/
def crowdEvent (b h j : ℕ) (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    Set (Fin n → ℝ × ℝ) :=
  {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ Wset b h j 𝒮)).card}

/-- The collections `𝒮` "of fewer than `M/b` inner regions, whether or not its regions are
heavy". -/
def smallCollections (b h j : ℕ) : Finset (Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :=
  Finset.univ.filter (fun 𝒮 => (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b)

/-- A region belongs to the collection `heavySet` exactly when it is heavy. -/
lemma mem_heavySet {b h j : ℕ} {P : Fin n → ℝ × ℝ} {p : Fin (b ^ j) × Fin (b ^ (h - j - 1))} :
    p ∈ heavySet b h j P ↔ Heavy b h j P p.1 p.2 := by
  simp [heavySet]

/-- A collection belongs to `smallCollections` exactly when it has fewer than `M/b`
regions. -/
lemma mem_smallCollections {b h j : ℕ} {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))} :
    𝒮 ∈ smallCollections b h j ↔ (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b := by
  simp [smallCollections]

/-- A point lies in `W_𝒮` exactly when it lies in a boundary strip or in a region of `𝒮`. -/
lemma mem_Wset {b h j : ℕ} {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))} {z : ℝ × ℝ} :
    z ∈ Wset b h j 𝒮 ↔
      z ∈ boundaryStrips b h j ∨ ∃ p ∈ 𝒮, z ∈ innerRegion b h j p.1 p.2 := by
  simp only [Wset, Set.mem_union, Set.mem_iUnion₂, exists_prop]

/-- "There are `b^j` old horizontal intervals and `b^{h-j-1}` new vertical intervals, hence
`M` comparison rectangles". -/
lemma card_compRect {b h j : ℕ} (hj : j < h) :
    Fintype.card (Fin (b ^ j) × Fin (b ^ (h - j - 1))) = b ^ (h - 1) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← pow_add]
  congr 1
  omega

/-- The bottom strip of the comparison rectangle `(c, v)` is an old cell: the product of the
`c`-th horizontal interval and of the vertical interval `b v` of stage `j`, which is the block
`B_1` of the `v`-th vertical interval of stage `j + 1` (`vcell_eq_block`). -/
lemma bottomStrip_eq (b h j c v : ℕ) :
    bottomStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ vcell b h j (b * v) := by
  unfold bottomStrip vcell vlen
  push_cast
  congr 2 <;> ring

/-- The top strip of the comparison rectangle `(c, v)` is an old cell: the product of the
`c`-th horizontal interval and of the vertical interval `b v + (b - 1)` of stage `j`, which is
the block `B_b` of the `v`-th vertical interval of stage `j + 1` (`vcell_eq_block`). -/
lemma topStrip_eq {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    topStrip b h j c v =
      Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
        vcell b h j (b * v + (b - 1)) := by
  unfold topStrip vcell vlen
  push_cast [Nat.cast_pred hb]
  congr 2 <;> ring

/-- The old cells of the comparison rectangle `(c, v)` other than the bottom and the top one,
that is, those with the vertical interval `b v + ℓ` of stage `j`, `1 ≤ ℓ ≤ b - 2` (the blocks
`B_2, …, B_{b-1}`), lie in its inner region. -/
lemma prod_vcell_subset_innerRegion {b : ℕ} (hb : 0 < b) (h j c v : ℕ) {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (h2 : ℓ + 2 ≤ b) :
    Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ vcell b h j (b * v + ℓ) ⊆
      innerRegion b h j c v := by
  have hL := vlen_pos hb h j
  -- the inner vertical interval is `[(b v + 1) b^{j-h}, (b v + b - 1) b^{j-h})`
  have e1 : ((v : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h =
      ((b : ℝ) * v + 1) * vlen b h j := by
    unfold vlen
    ring
  have e2 : (((v : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h =
      ((b : ℝ) * v + b - 1) * vlen b h j := by
    unfold vlen
    ring
  have h1R : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have h2R : (ℓ : ℝ) + 2 ≤ b := by exact_mod_cast h2
  rintro ⟨x, y⟩ ⟨hx, hy1, hy2⟩
  push_cast at hy1 hy2
  refine Set.mk_mem_prod hx ⟨?_, ?_⟩
  · rw [e1]
    exact (mul_le_mul_of_nonneg_right (by linarith) hL.le).trans hy1
  · rw [e2]
    exact hy2.trans_le (mul_le_mul_of_nonneg_right (by linarith) hL.le)

/-! ### 2. Fewer than `M/b` heavy regions -/

/-- "\[…\] no point lies in two inner regions": a point whose horizontal coordinate is not of
the form `k/b^j` lies in at most one inner region. (The horizontal intervals are closed, so
two neighbouring inner regions share a vertical segment.) -/
lemma innerRegion_inj {b h j : ℕ} (hb : 0 < b) {z : ℝ × ℝ}
    (hz : ∀ k : ℕ, z.1 ≠ (k : ℝ) / (b : ℝ) ^ j) {c c' v v' : ℕ}
    (h1 : z ∈ innerRegion b h j c v) (h2 : z ∈ innerRegion b h j c' v') : c = c' ∧ v = v' := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpj : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  have hpj1 : (0 : ℝ) < (b : ℝ) ^ (j + 1) := by positivity
  have hph : (0 : ℝ) < (b : ℝ) ^ h := by positivity
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := h1
  obtain ⟨⟨hx1', hx2'⟩, hy1', hy2'⟩ := h2
  -- two horizontal intervals with a common point that is not an endpoint
  have auxh : ∀ {a a' : ℕ}, (a : ℝ) / (b : ℝ) ^ j ≤ z.1 →
      z.1 ≤ ((a' : ℝ) + 1) / (b : ℝ) ^ j → a ≤ a' := by
    intro a a' ha ha'
    have hne := hz (a' + 1)
    push_cast at hne
    have hlt : (a : ℝ) / (b : ℝ) ^ j < ((a' : ℝ) + 1) / (b : ℝ) ^ j :=
      lt_of_le_of_lt ha (lt_of_le_of_ne ha' hne)
    have hlt' : (a : ℝ) < (a' : ℝ) + 1 := (div_lt_div_iff_of_pos_right hpj).mp hlt
    have : a < a' + 1 := by exact_mod_cast hlt'
    omega
  -- two inner vertical intervals with a common point
  have auxv : ∀ {a a' : ℕ}, ((a : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h ≤ z.2 →
      z.2 < (((a' : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h → a ≤ a' := by
    intro a a' ha ha'
    have hlt := (div_lt_div_iff_of_pos_right hph).mp (lt_of_le_of_lt ha ha')
    by_contra hcon
    have hcon' : (a' : ℝ) + 1 ≤ a := by exact_mod_cast not_le.mp hcon
    have := mul_le_mul_of_nonneg_right hcon' hpj1.le
    linarith
  exact ⟨le_antisymm (auxh hx1 hx2') (auxh hx1' hx2),
    le_antisymm (auxv hy1 hy2') (auxv hy1' hy2)⟩

/-- The inner regions of a collection hold at most `n` points in total, "since no point lies
in two inner regions".

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
lemma sum_innerCount_le {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ} (hgrid : NoGrid b P)
    (𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))) :
    ∑ p ∈ 𝒮, innerCount b h j P p.1 p.2 ≤ n := by
  -- the sets of the points in two different inner regions are disjoint
  have hdisj : (𝒮 : Set (Fin (b ^ j) × Fin (b ^ (h - j - 1)))).PairwiseDisjoint
      (fun p => Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)) := by
    intro p _ p' _ hne
    refine Finset.disjoint_left.mpr fun i hi hi' => hne ?_
    have hz : ∀ k : ℕ, (P i).1 ≠ (k : ℝ) / (b : ℝ) ^ j := fun k => by
      have := (hgrid i (k : ℤ) j).1
      push_cast at this
      exact this
    have := innerRegion_inj hb hz (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
    exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
  calc ∑ p ∈ 𝒮, innerCount b h j P p.1 p.2
      = (𝒮.biUnion fun p =>
          Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1 p.2)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-- "There are fewer than `M/b` heavy regions, since no point lies in two inner regions and
each heavy one contains more than `bn/M` of the `n` points."

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
theorem card_heavySet_lt {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ} (hgrid : NoGrid b P) :
    ((heavySet b h j P).card : ℝ) < (b : ℝ) ^ (h - 1) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  rcases (heavySet b h j P).eq_empty_or_nonempty with hH | hH
  · rw [hH, Finset.card_empty, Nat.cast_zero]
    positivity
  -- each heavy region contains more than `bn/M` points
  have h1 : ∑ _p ∈ heavySet b h j P, (b : ℝ) * n / (b : ℝ) ^ (h - 1) <
      ∑ p ∈ heavySet b h j P, (innerCount b h j P p.1 p.2 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hH fun p hp => mem_heavySet.mp hp
  -- no point lies in two inner regions
  have h2 : ∑ p ∈ heavySet b h j P, (innerCount b h j P p.1 p.2 : ℝ) ≤ n := by
    exact_mod_cast sum_innerCount_le hb hgrid (heavySet b h j P)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  -- so `|heavy| · bn/M < n`
  have h3 : ((heavySet b h j P).card : ℝ) * ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) < n :=
    lt_of_lt_of_le h1 h2
  have hn : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) h3
  rw [lt_div_iff₀ hbR]
  have h4 : ((heavySet b h j P).card : ℝ) * b * n < (b : ℝ) ^ (h - 1) * n := by
    have h5 : ((heavySet b h j P).card : ℝ) * ((b : ℝ) * n / (b : ℝ) ^ (h - 1)) =
        ((heavySet b h j P).card : ℝ) * b * n / (b : ℝ) ^ (h - 1) := by ring
    rw [h5, div_lt_iff₀ hM] at h3
    linarith
  exact lt_of_mul_lt_mul_right h4 hn.le

/-! ### 3. More than `n/2` points lie in `W` -/

/-- Every `x ∈ [0,1]` lies in one of the `b^j` horizontal intervals
`[c b^{-j}, (c+1) b^{-j}]` of stage `j`. -/
lemma exists_hcell {b : ℕ} (hb : 0 < b) (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c, c < b ^ j ∧ x ∈ Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hN : 0 < b ^ j := pow_pos hb j
  have hNR : (0 : ℝ) < (b : ℝ) ^ j := by positivity
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · -- `x < 1`: the interval `c = ⌊b^j x⌋`
    have h0 : 0 ≤ (b : ℝ) ^ j * x := mul_nonneg hNR.le hx.1
    refine ⟨⌊(b : ℝ) ^ j * x⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt h0]
      push_cast
      exact mul_lt_of_lt_one_right hNR hlt
    · rw [div_le_iff₀ hNR]
      linarith [Nat.floor_le h0]
    · rw [le_div_iff₀ hNR]
      linarith [Nat.lt_floor_add_one ((b : ℝ) ^ j * x)]
  · -- `x = 1`: the last interval, `c = b^j - 1`
    have hc : ((b ^ j - 1 : ℕ) : ℝ) = (b : ℝ) ^ j - 1 := by
      rw [Nat.cast_pred hN, Nat.cast_pow]
    refine ⟨b ^ j - 1, Nat.sub_lt hN one_pos, ?_, ?_⟩
    · rw [hc, heq, div_le_one hNR]
      linarith
    · rw [hc, heq, sub_add_cancel, div_self hNR.ne']

/-- Every height in `[0,1)` lies in one of the `b^{h-j}` vertical intervals
`[w b^{j-h}, (w+1) b^{j-h})` of stage `j`: the interval `w = ⌊b^{h-j} y⌋`. -/
lemma exists_vcell {b h j : ℕ} (hb : 0 < b) (hj : j ≤ h) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    ∃ w, w < b ^ (h - j) ∧ y ∈ vcell b h j w := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hL : (0 : ℝ) < (b : ℝ) ^ (h - j) := by positivity
  -- `b^{j-h} = 1 / b^{h-j}`
  have hvl : vlen b h j = 1 / (b : ℝ) ^ (h - j) := by
    unfold vlen
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add,
      Nat.add_sub_cancel' hj]
  have h0 : 0 ≤ (b : ℝ) ^ (h - j) * y := mul_nonneg hL.le hy.1
  refine ⟨⌊(b : ℝ) ^ (h - j) * y⌋₊, ?_, ?_, ?_⟩
  · rw [Nat.floor_lt h0]
    push_cast
    exact mul_lt_of_lt_one_right hL hy.2
  · rw [hvl, mul_one_div, div_le_iff₀ hL]
    linarith [Nat.floor_le h0]
  · rw [hvl, mul_one_div, lt_div_iff₀ hL]
    linarith [Nat.lt_floor_add_one ((b : ℝ) ^ (h - j) * y)]

/-- **The boundary strips and the inner regions cover `[0,1] × [0,1)`**: a point of
`[0,1] × [0,1)` lies in a boundary strip or in an inner region.

The point lies in an old cell: in a horizontal interval `c` and in a vertical interval `w` of
stage `j`. Write `w = b v + ℓ` with `ℓ < b`. For `ℓ = 0` and for `ℓ = b - 1` the old cell is a
boundary strip of the comparison rectangle `(c, v)`, and otherwise it lies in the inner region
of this rectangle. -/
theorem mem_boundaryStrips_or_innerRegion {b h j : ℕ} (hb : 0 < b) (hj : j < h) {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Set.Icc (0 : ℝ) 1) (hz2 : z.2 ∈ Set.Ico (0 : ℝ) 1) :
    z ∈ boundaryStrips b h j ∨
      ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)), z ∈ innerRegion b h j c v := by
  obtain ⟨c, hc, hx⟩ := exists_hcell hb j hz1
  obtain ⟨w, hw, hy⟩ := exists_vcell hb hj.le hz2
  -- `w = b v + ℓ` with `v = w / b < b^{h-j-1}` and `ℓ = w % b < b`
  have hv : w / b < b ^ (h - j - 1) := by
    rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]
    have : h - j - 1 + 1 = h - j := by omega
    rwa [this]
  have hℓ : w % b < b := Nat.mod_lt _ hb
  rw [← Nat.div_add_mod w b] at hy
  have hmem : z ∈ Set.Icc ((c : ℝ) / (b : ℝ) ^ j) (((c : ℝ) + 1) / (b : ℝ) ^ j) ×ˢ
      vcell b h j (b * (w / b) + w % b) := ⟨hx, hy⟩
  by_cases h0 : w % b = 0
  · -- the bottom old cell
    left
    rw [h0, add_zero, ← bottomStrip_eq] at hmem
    exact Set.mem_iUnion.mpr ⟨(⟨c, hc⟩, ⟨w / b, hv⟩), Or.inl hmem⟩
  by_cases h1 : w % b = b - 1
  · -- the top old cell
    left
    rw [h1, ← topStrip_eq hb] at hmem
    exact Set.mem_iUnion.mpr ⟨(⟨c, hc⟩, ⟨w / b, hv⟩), Or.inr hmem⟩
  · -- another old cell
    right
    exact ⟨⟨c, hc⟩, ⟨w / b, hv⟩,
      prod_vcell_subset_innerRegion hb h j c (w / b) (by omega) (by omega) hmem⟩

/-- On the probability-one event of Section 2.1 the points lie in `[0,1] × [0,1)`: no height
is `1 = 1/b^0`. -/
lemma mem_unit_of_inUnit_of_noGrid {b : ℕ} {P : Fin n → ℝ × ℝ} (hP : InUnit P)
    (hgrid : NoGrid b P) (i : Fin n) :
    (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  have h1 := (hgrid i 1 0).2
  simp only [Int.cast_one, pow_zero, div_one] at h1
  exact ⟨⟨(hP i).1.1.le, (hP i).1.2⟩, ⟨(hP i).2.1.le, lt_of_le_of_ne (hP i).2.2 h1⟩⟩

/-- "Every other point lies in a heavy inner region or in a boundary strip": a point of
`[0,1] × [0,1)` that does not lie in an inner region that is not heavy lies in `W`. -/
theorem mem_Wset_heavySet {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ} {i : Fin n}
    (hi1 : (P i).1 ∈ Set.Icc (0 : ℝ) 1) (hi2 : (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hi : ¬ ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
      P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v) :
    P i ∈ Wset b h j (heavySet b h j P) := by
  rcases mem_boundaryStrips_or_innerRegion hb hj hi1 hi2 with hs | ⟨c, v, hin⟩
  · exact mem_Wset.mpr (Or.inl hs)
  · have hheavy : Heavy b h j P c v := by
      by_contra hnh
      exact hi ⟨c, v, hin, hnh⟩
    exact mem_Wset.mpr (Or.inr ⟨(c, v), (mem_heavySet (p := (c, v))).mpr hheavy, hin⟩)

/-- "Suppose that `G_j` fails, that is, fewer than `n/2` points lie in inner regions that are
not heavy. Every other point lies in a heavy inner region or in a boundary strip \[…\]. So
more than `n/2` points lie in the union `W` of the boundary strips and the heavy regions."

Needs that the points lie in `[0,1] × [0,1)`. -/
theorem half_lt_card_Wset {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ}
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hbad : ¬ GoodTransition b h j P) :
    (n : ℝ) / 2 <
      (Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P))).card := by
  -- the points in inner regions that are not heavy, and the other points
  set light : Finset (Fin n) := Finset.univ.filter (fun i => ∃ c : Fin (b ^ j),
    ∃ v : Fin (b ^ (h - j - 1)), P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
  set other : Finset (Fin n) := Finset.univ.filter (fun i => ¬ ∃ c : Fin (b ^ j),
    ∃ v : Fin (b ^ (h - j - 1)), P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
  -- `G_j` fails: fewer than `n/2` points lie in inner regions that are not heavy
  have hfew : (light.card : ℝ) < (n : ℝ) / 2 := not_le.mp hbad
  have hsplit : (light.card : ℝ) + other.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ innerRegion b h j c v ∧ ¬ Heavy b h j P c v)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  -- every other point lies in `W`
  have hsub : other ⊆ Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mem_Wset_heavySet hb hj (hP i).1 (hP i).2 (Finset.mem_filter.mp hi).2⟩
  have hle : (other.card : ℝ) ≤
      (Finset.univ.filter (fun i => P i ∈ Wset b h j (heavySet b h j P))).card := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-! ### 4. `W_𝒮` has area at most `3/b` -/

/-- The area of a rectangle. -/
lemma volume_Icc_prod_Ico {a c : ℝ} (hac : a ≤ c) (d e : ℝ) :
    volume (Set.Icc a c ×ˢ Set.Ico d e) = ENNReal.ofReal ((c - a) * (e - d)) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ico,
    ENNReal.ofReal_mul (sub_nonneg.mpr hac)]

/-- A bottom strip is an old cell, of area `b^{-j} · b^{j-h} = b^{-h} = 1/(bM)`. -/
lemma volume_bottomStrip {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (bottomStrip b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold bottomStrip
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- A top strip is an old cell, of area `b^{-j} · b^{j-h} = b^{-h} = 1/(bM)`. -/
lemma volume_topStrip {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (topStrip b h j c v) = ENNReal.ofReal (1 / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold topStrip
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- An inner region has area `b^{-j} · (b - 2) b^{j-h} = (b - 2) b^{-h} = (b - 2)/(bM)`. -/
lemma volume_innerRegion {b : ℕ} (hb : 0 < b) (h j c v : ℕ) :
    volume (innerRegion b h j c v) = ENNReal.ofReal (((b : ℝ) - 2) / (b : ℝ) ^ h) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold innerRegion
  rw [volume_Icc_prod_Ico (div_le_div_of_nonneg_right (by linarith) (by positivity))]
  congr 1
  field_simp
  ring

/-- `b^h = b M`. -/
lemma pow_eq_mul_pow_pred {b h : ℕ} (hh : 0 < h) : (b : ℝ) ^ h = b * (b : ℝ) ^ (h - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- "The regions in `𝒮` have area less than `1/M` each". -/
lemma volume_innerRegion_lt {b h : ℕ} (hb : 0 < b) (hh : 0 < h) (j c v : ℕ) :
    volume (innerRegion b h j c v) < ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : (0 : ℝ) < (b : ℝ) ^ (h - 1) := by positivity
  rw [volume_innerRegion hb, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    pow_eq_mul_pow_pred hh, div_lt_div_iff₀ (by positivity) hM]
  linarith

/-- The boundary strips cover an area of at most `2/b`, for every `b ≥ 1`: there are `M`
comparison rectangles, each of them has two boundary strips, and an old cell has area
`1/(bM)`. This bound is used for `volume_Wset_le`. The sentence "The boundary strips are two
of the `b` old cells of every comparison rectangle, so they cover an area of `2/b`" is
`volume_boundaryStrips`: for `b ≥ 2` the area is equal to `2/b`. -/
theorem volume_boundaryStrips_le {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    volume (boundaryStrips b h j) ≤ ENNReal.ofReal (2 / (b : ℝ)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  calc volume (boundaryStrips b h j)
      ≤ ∑ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)),
          volume (bottomStrip b h j p.1 p.2 ∪ topStrip b h j p.1 p.2) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin (b ^ j) × Fin (b ^ (h - j - 1)), ENNReal.ofReal (2 / (b : ℝ) ^ h) := by
        refine Finset.sum_le_sum fun p _ => (measure_union_le _ _).trans ?_
        rw [volume_bottomStrip hb, volume_topStrip hb,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        ring
    _ = ENNReal.ofReal (2 / (b : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, card_compRect hj, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        rw [pow_eq_mul_pow_pred (by omega : 0 < h)]
        field_simp

/-- "The regions in `𝒮` have area less than `1/M` each, so they cover an area of less than
`1/b`", for a collection `𝒮` of fewer than `M/b` inner regions. The inequality is strict
because there are fewer than `M/b` regions; this covers the empty collection. -/
theorem volume_innerRegions_lt {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) < ENNReal.ofReal (1 / (b : ℝ)) := by
  calc volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2)
      ≤ ∑ p ∈ 𝒮, volume (innerRegion b h j p.1 p.2) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ 𝒮, ENNReal.ofReal (1 / (b : ℝ) ^ (h - 1)) :=
        Finset.sum_le_sum fun p _ => (volume_innerRegion_lt hb (by omega) j p.1 p.2).le
    _ = ENNReal.ofReal (𝒮.card * (1 / (b : ℝ) ^ (h - 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal (1 / (b : ℝ)) := by
        -- there are fewer than `M/b` regions
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        calc (𝒮.card : ℝ) * (1 / (b : ℝ) ^ (h - 1))
            < (b : ℝ) ^ (h - 1) / b * (1 / (b : ℝ) ^ (h - 1)) :=
              mul_lt_mul_of_pos_right h𝒮 (by positivity)
          _ = 1 / (b : ℝ) := by field_simp

/-- "Hence `W_𝒮` is a fixed set of area at most `3/b`", for every collection `𝒮` of fewer
than `M/b` inner regions: the boundary strips cover an area of at most `2/b`
(`volume_boundaryStrips_le`; equal to `2/b` for `b ≥ 2`, `volume_boundaryStrips`), and the
regions in `𝒮` cover an area of less than `1/b` (`volume_innerRegions_lt`). -/
theorem volume_Wset_le {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    volume (Wset b h j 𝒮) ≤ ENNReal.ofReal (3 / (b : ℝ)) := by
  calc volume (Wset b h j 𝒮)
      ≤ volume (boundaryStrips b h j) + volume (⋃ p ∈ 𝒮, innerRegion b h j p.1 p.2) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 / (b : ℝ)) + ENNReal.ofReal (1 / (b : ℝ)) :=
        add_le_add (volume_boundaryStrips_le hb hj) (volume_innerRegions_lt hb hj h𝒮).le
    _ = ENNReal.ofReal (3 / (b : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The area of `W_𝒮`**, for the law of one uniform point of the unit square: a uniform
point of `[0,1]²` lies in `W_𝒮` with probability at most `3/b`, for every collection `𝒮` of
fewer than `M/b` inner regions. -/
theorem unitSq_Wset_le {b h j : ℕ} (hb : 0 < b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) (Wset b h j 𝒮) ≤ ENNReal.ofReal (3 / (b : ℝ)) :=
  (Measure.restrict_apply_le _ _).trans (volume_Wset_le hb hj h𝒮)

/-! ### 5. The probability of `E_𝒮` -/

/-- "The `n` points are independent and uniform in the unit square": the points of a given set
`T` of indices all lie in a fixed set `W` with probability `|W|^{|T|}`, where `|W|` is the
probability that one uniform point lies in `W`. -/
theorem unifPts_forall_mem (T : Finset (Fin n)) (W : Set (ℝ × ℝ)) :
    unifPts n {P | ∀ i ∈ T, P i ∈ W} =
      (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := by
  -- the event is a box
  have hset : {P : Fin n → ℝ × ℝ | ∀ i ∈ T, P i ∈ W} =
      Set.univ.pi (fun i => if i ∈ T then W else Set.univ) := by
    ext P
    rw [Set.mem_ofPred_eq, Set.mem_univ_pi]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ T <;> simp [hi]
  rw [hset, Measure.pi_pi]
  calc ∏ i : Fin n, (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) (if i ∈ T then W else Set.univ)
      = ∏ i : Fin n, if i ∈ T then (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W else 1 := by
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs
        · rfl
        · exact measure_univ
    _ = (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := by
        rw [Fintype.prod_ite_mem, Finset.prod_const]

/-- "\[…\] the points of a given set all lie in the fixed set `W_𝒮` with probability at most
`(3/b)^{⌈n/2⌉} ≤ (3/b)^{n/2}`, since `3/b ≤ 1`": here for a set `W` in which a uniform point
lies with probability at most `q ≤ 1`, and for a set `T` of at least `n/2` indices. -/
theorem unifPts_forall_mem_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)}
    (hW : (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q)
    {T : Finset (Fin n)} (hT : (n : ℝ) / 2 ≤ T.card) :
    unifPts n {P | ∀ i ∈ T, P i ∈ W} ≤ ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
  calc unifPts n {P | ∀ i ∈ T, P i ∈ W}
      = (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ^ T.card := unifPts_forall_mem T W
    _ ≤ ENNReal.ofReal q ^ T.card := pow_le_pow_left' hW _
    _ = ENNReal.ofReal (q ^ ((T.card : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast, ENNReal.ofReal_pow hq0.le]
    _ ≤ ENNReal.ofReal (q ^ ((n : ℝ) / 2)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hT)

/-- "If `E_𝒮` occurs, then there is a set of `⌈n/2⌉` indices whose points all lie in
`W_𝒮`." -/
lemma exists_card_eq_ceil_half {W : Set (ℝ × ℝ)} {P : Fin n → ℝ × ℝ}
    (hE : (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card) :
    ∃ T : Finset (Fin n), T.card = ⌈(n : ℝ) / 2⌉₊ ∧ ∀ i ∈ T, P i ∈ W := by
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.mpr hE)
  exact ⟨T, hTcard, fun i hi => (Finset.mem_filter.mp (hTsub hi)).2⟩

/-- "There are at most `2^n` sets of indices. \[…\] So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`": if a
uniform point lies in a fixed set `W` with probability at most `q ≤ 1`, then at least `n/2` of
the `n` points lie in `W` with probability at most `2^n q^{n/2}`. -/
theorem unifPts_half_mem_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {W : Set (ℝ × ℝ)}
    (hW : (volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)) W ≤ ENNReal.ofReal q) :
    unifPts n {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card} ≤
      ENNReal.ofReal (2 ^ n * q ^ ((n : ℝ) / 2)) := by
  -- the sets of `⌈n/2⌉` indices
  let 𝒯 : Finset (Finset (Fin n)) := Finset.univ.filter (fun T => T.card = ⌈(n : ℝ) / 2⌉₊)
  -- if the event occurs, then the points of one of these sets all lie in `W`
  have hsub : {P : Fin n → ℝ × ℝ | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card} ⊆
      ⋃ T ∈ 𝒯, {P | ∀ i ∈ T, P i ∈ W} := by
    intro P hP
    obtain ⟨T, hT, hTW⟩ := exists_card_eq_ceil_half hP
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩) hTW
  -- there are at most `2^n` sets of indices
  have hcard : 𝒯.card ≤ 2 ^ n := by
    calc 𝒯.card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  calc unifPts n {P | (n : ℝ) / 2 ≤ (Finset.univ.filter (fun i => P i ∈ W)).card}
      ≤ unifPts n (⋃ T ∈ 𝒯, {P | ∀ i ∈ T, P i ∈ W}) := measure_mono hsub
    _ ≤ ∑ T ∈ 𝒯, unifPts n {P | ∀ i ∈ T, P i ∈ W} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ 𝒯, ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun T hT => unifPts_forall_mem_le hq0 hq1 hW ?_
        rw [(Finset.mem_filter.mp hT).2]
        exact Nat.le_ceil _
    _ = (𝒯.card : ENNReal) * ENNReal.ofReal (q ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ n : ℕ) : ENNReal) * ENNReal.ofReal (q ^ ((n : ℝ) / 2)) :=
        mul_le_mul' (Nat.cast_le.mpr hcard) le_rfl
    _ = ENNReal.ofReal (2 ^ n * q ^ ((n : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Nat.cast_pow,
          Nat.cast_ofNat]

/-- "So `Pr(E_𝒮) ≤ 2^n (3/b)^{n/2}`", for every collection `𝒮` of fewer than `M/b` inner
regions. -/
theorem unifPts_crowdEvent_le {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h)
    {𝒮 : Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1)))}
    (h𝒮 : (𝒮.card : ℝ) < (b : ℝ) ^ (h - 1) / b) :
    unifPts n (crowdEvent b h j 𝒮) ≤
      ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hq0 : (0 : ℝ) < 3 / (b : ℝ) := by positivity
  -- `3/b ≤ 1`
  have hq1 : 3 / (b : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hbR
  exact unifPts_half_mem_le hq0 hq1 (unitSq_Wset_le (by omega) hj h𝒮)

/-! ### 6. The union bounds -/

/-- "We have just seen that if `G_j` fails, then `E_𝒮` occurs for the collection `𝒮` of heavy
regions."

Needs that the points lie in `[0,1] × [0,1)`. -/
theorem mem_crowdEvent_heavySet {b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Fin n → ℝ × ℝ}
    (hP : ∀ i, (P i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (P i).2 ∈ Set.Ico (0 : ℝ) 1)
    (hbad : ¬ GoodTransition b h j P) : P ∈ crowdEvent b h j (heavySet b h j P) :=
  (half_lt_card_Wset hb hj hP hbad).le

/-- The collection of the heavy regions is a collection of fewer than `M/b` inner regions.

Needs that no horizontal coordinate of a point has the form `k/b^j` (from `NoGrid`). -/
theorem heavySet_mem_smallCollections {b h j : ℕ} (hb : 0 < b) {P : Fin n → ℝ × ℝ}
    (hgrid : NoGrid b P) : heavySet b h j P ∈ smallCollections b h j :=
  mem_smallCollections.mpr (card_heavySet_lt hb hgrid)

/-- "So `G_j^c` is contained in the union of the events `E_𝒮`", over the collections `𝒮` of
fewer than `M/b` inner regions; on the probability-one event of Section 2.1 (`InUnit`,
`NoGrid`). -/
theorem bad_subset_iUnion_crowdEvent {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    {P : Fin n → ℝ × ℝ | ¬ GoodTransition b h j P} ∩ {P | InUnit P ∧ NoGrid b P} ⊆
      ⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮 := by
  rintro P ⟨hbad, hP, hgrid⟩
  exact Set.mem_biUnion (heavySet_mem_smallCollections hb hgrid)
    (mem_crowdEvent_heavySet hb hj (mem_unit_of_inUnit_of_noGrid hP hgrid) hbad)

/-- "So `G_j^c` is contained in the union of the events `E_𝒮`", almost surely. -/
theorem bad_ae_le_iUnion_crowdEvent {b h j : ℕ} (hb : 0 < b) (hj : j < h) :
    {P : Fin n → ℝ × ℝ | ¬ GoodTransition b h j P} ≤ᵐ[unifPts n]
      ⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮 := by
  filter_upwards [ae_inUnit n, ae_noGrid n b] with P hP hgrid hbad
  exact bad_subset_iUnion_crowdEvent hb hj ⟨hbad, hP, hgrid⟩

/-- "There are at most `2^M` collections of inner regions". -/
lemma card_smallCollections_le {b h j : ℕ} (hj : j < h) :
    (smallCollections b h j).card ≤ 2 ^ b ^ (h - 1) := by
  calc (smallCollections b h j).card
      ≤ (Finset.univ : Finset (Finset (Fin (b ^ j) × Fin (b ^ (h - j - 1))))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ b ^ (h - 1) := by rw [Finset.card_univ, Fintype.card_finset, card_compRect hj]

/-- "There are at most `2^M` collections of inner regions, so
`Pr(G_j^c) ≤ 2^{M+n} (3/b)^{n/2}`." -/
theorem unifPts_bad_le {b h j : ℕ} (hb : 3 ≤ b) (hj : j < h) :
    unifPts n {P | ¬ GoodTransition b h j P} ≤
      ENNReal.ofReal (2 ^ (b ^ (h - 1) + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
  calc unifPts n {P | ¬ GoodTransition b h j P}
      ≤ unifPts n (⋃ 𝒮 ∈ smallCollections b h j, crowdEvent b h j 𝒮) :=
        measure_mono_ae (bad_ae_le_iUnion_crowdEvent (by omega) hj)
    _ ≤ ∑ 𝒮 ∈ smallCollections b h j, unifPts n (crowdEvent b h j 𝒮) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _𝒮 ∈ smallCollections b h j,
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
        Finset.sum_le_sum fun 𝒮 h𝒮 => unifPts_crowdEvent_le hb hj (mem_smallCollections.mp h𝒮)
    _ = ((smallCollections b h j).card : ENNReal) *
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ b ^ (h - 1) : ℕ) : ENNReal) *
          ENNReal.ofReal (2 ^ n * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
        mul_le_mul' (Nat.cast_le.mpr (card_smallCollections_le hj)) le_rfl
    _ = ENNReal.ofReal (2 ^ (b ^ (h - 1) + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring

/-- "Since `M ≤ n`, we have `2^{M+n} ≤ 4^n = 16^{n/2}`, which gives `(48/b)^{n/2}`." -/
lemma two_pow_mul_rpow_le {b M : ℕ} (hb : 0 < b) (hMn : M ≤ n) :
    (2 : ℝ) ^ (M + n) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2) ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  -- `2^{M+n} ≤ 4^n`
  have h1 : (2 : ℝ) ^ (M + n) ≤ 4 ^ n := by
    calc (2 : ℝ) ^ (M + n) ≤ 2 ^ (2 * n) := pow_le_pow_right₀ one_le_two (by omega)
      _ = 4 ^ n := by
          rw [pow_mul]
          norm_num
  -- `4^n = 16^{n/2}`
  have h2 : (4 : ℝ) ^ n = (16 : ℝ) ^ ((n : ℝ) / 2) := by
    have h16 : (16 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      norm_num
    rw [h16, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    ring
  -- `16^{n/2} (3/b)^{n/2} = (48/b)^{n/2}`
  have h3 : (48 / (b : ℝ)) ^ ((n : ℝ) / 2) =
      (16 : ℝ) ^ ((n : ℝ) / 2) * (3 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  rw [h3, ← h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- `Pr(G_j^c) ≤ (48/b)^{n/2}` if `M ≤ n`, as an inequality in `[0, ∞]`. -/
theorem unifPts_bad_le_rpow {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h) :
    unifPts n {P | ¬ GoodTransition b h j P} ≤
      ENNReal.ofReal ((48 / (b : ℝ)) ^ ((n : ℝ) / 2)) :=
  (unifPts_bad_le hb hj).trans
    (ENNReal.ofReal_le_ofReal (two_pow_mul_rpow_le (by omega) hMn))

/-- **Lemma 2.5(ii), one transition**, by the proof of the manuscript: if `M ≤ n`, then
`Pr(G_j^c) ≤ (48/b)^{n/2}`. -/
theorem lemma_2_5_ii {b h j : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) (hj : j < h) :
    (unifPts n).real {P | ¬ GoodTransition b h j P} ≤ (48 / (b : ℝ)) ^ ((n : ℝ) / 2) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (unifPts_bad_le_rpow hb hMn hj)

/-- **Lemma 2.5(ii), all transitions**: if `M ≤ n`, then `Pr(G^c) ≤ h (48/b)^{n/2}`.

"A union bound over the `h` transitions gives the bound on `Pr(G^c)`." -/
theorem lemma_2_5_ii_all {b h : ℕ} (hb : 3 ≤ b) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
  -- `G^c` is the union of the events `G_j^c`, `j < h`
  have hset : {P : Fin n → ℝ × ℝ | ∃ j, j < h ∧ ¬ GoodTransition b h j P} =
      ⋃ j ∈ Finset.range h, {P | ¬ GoodTransition b h j P} := by
    ext P
    simp
  rw [hset]
  calc (unifPts n).real (⋃ j ∈ Finset.range h, {P | ¬ GoodTransition b h j P})
      ≤ ∑ j ∈ Finset.range h, (unifPts n).real {P | ¬ GoodTransition b h j P} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range h, (48 / (b : ℝ)) ^ ((n : ℝ) / 2) :=
        Finset.sum_le_sum fun j hj => lemma_2_5_ii hb hMn (Finset.mem_range.mp hj)
    _ = h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end R56Audit
end

section
/-!
# Conditional expectations given random elements that determine each other almost surely

Auditor's supplement (not part of the audited archive).

A σ-field of the manuscript is described by its generators ("the σ-field generated by all
heights and by the first `j` base-`b` digits of every horizontal coordinate"), and the same
information can be encoded by other random elements ("The first `j` digits of `U_i` determine
the stage-`j` horizontal interval that contains `U_i`."). On the probability-one event of
Section 2.1 the two encodings determine each other. `condExp_comap_congr_ae` says that
conditional expectations do not see the difference.
-/

namespace R56Audit

open MeasureTheory

noncomputable section

/-- **Almost surely equivalent generators give the same conditional expectations.** If
`f₂ = e ∘ f₁` and `f₁ = e' ∘ f₂` almost surely, with `e`, `e'` measurable, then conditional
expectations given `f₁` and given `f₂` agree almost surely. -/
theorem condExp_comap_congr_ae {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure Ω} [IsFiniteMeasure μ] {f₁ : Ω → α} {f₂ : Ω → β}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) {e : α → β} {e' : β → α} (he : Measurable e)
    (he' : Measurable e') (h₁₂ : f₂ =ᵐ[μ] e ∘ f₁) (h₂₁ : f₁ =ᵐ[μ] e' ∘ f₂) (X : Ω → ℝ) :
    μ[X | MeasurableSpace.comap f₁ inferInstance] =ᵐ[μ]
      μ[X | MeasurableSpace.comap f₂ inferInstance] := by
  by_cases hX : Integrable X μ
  swap
  · rw [condExp_of_not_integrable hX, condExp_of_not_integrable hX]
  refine ae_eq_condExp_of_forall_setIntegral_eq hf₂.comap_le hX
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_) ?_
  · -- an event of `f₂` is almost surely an event of `f₁`
    obtain ⟨B, hB, rfl⟩ := hs
    have hset : f₂ ⁻¹' B =ᵐ[μ] f₁ ⁻¹' (e ⁻¹' B) := by
      filter_upwards [h₁₂] with ω hω
      change (f₂ ω ∈ B) = (e (f₁ ω) ∈ B)
      rw [hω]
      rfl
    rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
    exact setIntegral_condExp hf₁.comap_le hX ⟨e ⁻¹' B, he hB, rfl⟩
  · -- a function of `f₁` is almost surely a function of `f₂` (Doob–Dynkin)
    have hsm : StronglyMeasurable[MeasurableSpace.comap f₁ inferInstance]
        (μ[X | MeasurableSpace.comap f₁ inferInstance]) := stronglyMeasurable_condExp
    obtain ⟨φ, hφ, hφeq⟩ := StronglyMeasurable.exists_eq_measurable_comp hsm
    refine ⟨fun ω => φ (e' (f₂ ω)),
      (hφ.comp_measurable he').comp_measurable (comap_measurable f₂), ?_⟩
    filter_upwards [h₂₁] with ω hω
    rw [hφeq]
    change φ (f₁ ω) = φ (e' (f₂ ω))
    rw [hω]
    rfl

end

end R56Audit
end

section
/-!
# The σ-field generated by the heights and the first `j` digits

Auditor's supplement (not part of the audited archive).

Section 2.4: "Let `𝓕_j` be the σ-field generated by all heights and by the first `j` base-`b`
digits of every horizontal coordinate. The first `j` digits of `U_i` determine the stage-`j`
horizontal interval that contains `U_i`."

`StageFiltration.lean` takes for `𝓕_j` the σ-field `stageSigma n b j` generated by the heights
and by the index of the stage-`j` interval `(c b^{-j}, (c+1) b^{-j}]` that contains each
`U_i`. This file defines the base-`b` digits themselves (`digit b k u = ⌊b^k u⌋ mod b`) and
the σ-field `digitSigma n b j` generated by all heights and the first `j` digits of every
horizontal coordinate, and proves that the difference is invisible:

* `fresh_eq_digit`: for a positive number that is not of the form `m/b^r`, the next digit at
  stage `k` (the index of the child of its stage-`k` interval that contains it) is its
  `(k+1)`-st base-`b` digit;
* `coarseInfo_ae_eq_digitInfo`, `digitInfo_ae_eq_coarseInfo`: almost surely, the heights and
  the stage-`j` indices are a measurable function of the heights and the first `j` digits, and
  conversely;
* `condExp_digitSigma`: conditional expectations given `digitSigma n b j` and given
  `stageSigma n b j` are almost surely equal;
* `lemma_2_4_digits`, `lemma_2_6_digits`: Lemmas 2.4 and 2.6 with the σ-fields of the digits;
* `roadmap_digits`: display (10) with the σ-fields of the digits;
* `Zpot_aestronglyMeasurable_digits`: "So `Z_j` is `𝓕_j`-measurable", for the σ-field of the
  digits: `Z_j` is almost surely equal to a `digitSigma n b j`-measurable function;
* `nextDigits`, `condExp_nextDigits`: "The `(j+1)`-st digits, which we call the next digits at
  stage `j`, are independent and uniform conditional on `𝓕_j`", for the σ-field of the digits:
  the conditional expectation, given `digitSigma n b j`, of a bounded function of the heights,
  the first `j` digits and the next digits is its average over all values of the next digits.
-/

namespace R56Audit

open MeasureTheory Riesz Riesz.PointSets Oscillation

noncomputable section

variable {n : ℕ}

/-- The `k`-th base-`b` digit of `u`, for `k ≥ 1`: `⌊b^k u⌋ mod b`. For `u ∈ [0,1)` these are
the digits of the expansion `u = Σ_{k ≥ 1} d_k b^{-k}`. -/
def digit (b k : ℕ) (u : ℝ) : ℕ := ⌊(b : ℝ) ^ k * u⌋₊ % b

/-- All heights, and the first `j` base-`b` digits of every horizontal coordinate. -/
def digitInfo (n b j : ℕ) (P : Fin n → ℝ × ℝ) : (Fin n → ℝ) × (Fin n → Fin j → ℕ) :=
  (fun i => (P i).2, fun i k => digit b ((k : ℕ) + 1) (P i).1)

/-- The σ-field generated by all heights and by the first `j` base-`b` digits of every
horizontal coordinate. -/
abbrev digitSigma (n b j : ℕ) : MeasurableSpace (Fin n → ℝ × ℝ) :=
  MeasurableSpace.comap (digitInfo n b j) inferInstance

/-- Every digit is a measurable function of the number. -/
lemma measurable_digit (b k : ℕ) : Measurable (digit b k) :=
  (measurable_of_countable fun m : ℕ => m % b).comp
    (measurable_const.mul measurable_id).nat_floor

lemma measurable_digitInfo (n b j : ℕ) : Measurable (digitInfo n b j) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun i => ?_)
    (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_)
  · exact measurable_snd.comp (measurable_pi_apply i)
  · exact (measurable_digit b ((k : ℕ) + 1)).comp (measurable_fst.comp (measurable_pi_apply i))

/-- For a positive number that is not of the form `m/b^r`, the next digit at stage `k` is the
`(k+1)`-st base-`b` digit. -/
theorem fresh_eq_digit {b : ℕ} (hb : 0 < b) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (hgrid : ∀ (m : ℤ) (r : ℕ), u ≠ (m : ℝ) / (b : ℝ) ^ r) :
    (freshGridIndex (b ^ k) b hb u : ℕ) = digit b (k + 1) u := by
  have hpow : (0 : ℝ) < (b : ℝ) ^ (k + 1) := pow_pos (Nat.cast_pos.mpr hb) _
  -- `b^(k+1) u` is not an integer, so its ceiling is its floor plus one
  have hceil : ⌈(b : ℝ) ^ (k + 1) * u⌉ = ⌊(b : ℝ) ^ (k + 1) * u⌋ + 1 := by
    rw [Int.ceil_eq_floor_add_one_iff_notMem]
    rintro ⟨m, hm⟩
    refine hgrid m (k + 1) ?_
    rw [hm]
    exact (mul_div_cancel_left₀ u hpow.ne').symm
  -- hence the index of the stage-`(k+1)` interval that contains `u` is `⌊b^(k+1) u⌋`
  have hidx : gridIndex (b ^ k * b) u = ⌊(b : ℝ) ^ (k + 1) * u⌋ := by
    unfold gridIndex
    rw [Nat.cast_mul, Nat.cast_pow, ← pow_succ, hceil, add_sub_cancel_right]
  -- the next digit is the remainder of this index modulo `b`; compare the two sides in `ℤ`
  apply Nat.cast_injective (R := ℤ)
  rw [freshGridIndex_eq_emod (b ^ k) b (pow_pos hb k) hb u, hidx, digit, Int.natCast_emod,
    Int.natCast_floor_eq_floor (mul_pos hpow hu).le]

/-- The integer whose base-`b` expansion consists of the digits `d 0, …, d (j - 1)`, the most
significant digit first: `Σ_{k < j} b^(j-(k+1)) d_k`. -/
def idxOfDigits (b j : ℕ) (d : Fin j → ℕ) : ℤ :=
  ∑ k : Fin j, (b : ℤ) ^ (j - ((k : ℕ) + 1)) * (d k : ℤ)

/-- The integer with the digits `d 0, …, d j` is `b` times the integer with the digits
`d 0, …, d (j - 1)`, plus the last digit `d j`. -/
lemma idxOfDigits_succ (b j : ℕ) (d : Fin (j + 1) → ℕ) :
    idxOfDigits b (j + 1) d =
      (b : ℤ) * idxOfDigits b j (fun k => d k.castSucc) + (d (Fin.last j) : ℤ) := by
  unfold idxOfDigits
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.val_castSucc, Nat.sub_add_comm (Nat.succ_le_of_lt k.isLt), pow_succ', mul_assoc]
  · rw [Fin.val_last, Nat.sub_self, pow_zero, one_mul]

/-- "The first `j` digits of `U_i` determine the stage-`j` horizontal interval that contains
`U_i`": for a number of `(0,1]` that is not of the form `m/b^r`, the index of its stage-`j`
interval is the integer whose base-`b` expansion consists of its first `j` digits. -/
lemma gridIndex_eq_idxOfDigits {b : ℕ} (hb : 0 < b) (j : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) (hgrid : ∀ (m : ℤ) (r : ℕ), u ≠ (m : ℝ) / (b : ℝ) ^ r) :
    gridIndex (b ^ j) u = idxOfDigits b j (fun k => digit b ((k : ℕ) + 1) u) := by
  induction j with
  | zero =>
    -- the only interval of stage `0` is `(0, 1]`, with index `0`
    have h := gridIndex_bounds 1 one_pos hu
    have h0 : (0 : ℤ) ≤ gridIndex 1 u := by exact_mod_cast h.1
    have h1 : gridIndex 1 u + 1 ≤ 1 := by exact_mod_cast h.2
    rw [pow_zero, idxOfDigits, Fin.sum_univ_zero]
    omega
  | succ j ih =>
    -- the index of stage `j + 1` is `b` times the index of stage `j` plus the next digit
    rw [gridIndex_succ hb, ih, fresh_eq_digit hb j hu.1 hgrid, idxOfDigits_succ b j]
    rfl

/-- The last `j` base-`b` digits of the integer `g`, the most significant digit first: the
entry `k` is the digit of weight `b^(j-(k+1))`. -/
def digitsOfIdx (b j : ℕ) (g : ℤ) (k : Fin j) : ℕ :=
  ((g / (b : ℤ) ^ (j - ((k : ℕ) + 1))) % (b : ℤ)).toNat

/-- Conversely, the stage-`j` interval determines the first `j` digits: for a positive number
that is not of the form `m/b^r`, the first `j` digits are the base-`b` digits of the index of
its stage-`j` interval. -/
lemma digit_eq_digitsOfIdx {b : ℕ} (hb : 0 < b) (j : ℕ) {u : ℝ} (hu : 0 < u)
    (hgrid : ∀ (m : ℤ) (r : ℕ), u ≠ (m : ℝ) / (b : ℝ) ^ r) (k : Fin j) :
    digit b ((k : ℕ) + 1) u = digitsOfIdx b j (gridIndex (b ^ j) u) k := by
  -- the quotient of the stage-`j` index by `b^(j-(k+1))` is the stage-`(k+1)` index
  have h1 := gridIndex_mul_ediv (b ^ ((k : ℕ) + 1)) (b ^ (j - ((k : ℕ) + 1))) (pow_pos hb _) u
  rw [pow_mul_pow_sub b (Nat.succ_le_of_lt k.isLt), Nat.cast_pow] at h1
  -- and the remainder of the stage-`(k+1)` index modulo `b` is the next digit at stage `k`
  have h2 := freshGridIndex_eq_emod (b ^ (k : ℕ)) b (pow_pos hb _) hb u
  rw [← pow_succ] at h2
  rw [digitsOfIdx, h1, ← h2, Int.toNat_natCast, fresh_eq_digit hb k hu hgrid]

/-- The heights and the stage-`j` indices, read from the heights and the first `j` digits: the
heights are kept, and the index of a point is the integer whose base-`b` expansion consists of
its first `j` digits. -/
def coarseOfDigits (n b j : ℕ) (p : (Fin n → ℝ) × (Fin n → Fin j → ℕ)) :
    (Fin n → ℝ) × (Fin n → ℤ) :=
  (p.1, fun i => idxOfDigits b j (p.2 i))

/-- The heights and the first `j` digits, read from the heights and the stage-`j` indices: the
heights are kept, and the digits of a point are the last `j` base-`b` digits of its index. -/
def digitsOfCoarse (n b j : ℕ) (p : (Fin n → ℝ) × (Fin n → ℤ)) :
    (Fin n → ℝ) × (Fin n → Fin j → ℕ) :=
  (p.1, fun i => digitsOfIdx b j (p.2 i))

/-- The indices are a measurable function of the digits; the heights are kept. -/
lemma measurable_coarseOfDigits (n b j : ℕ) : Measurable (coarseOfDigits n b j) :=
  measurable_fst.prodMk ((measurable_of_countable
    (fun d : Fin n → Fin j → ℕ => fun i => idxOfDigits b j (d i))).comp measurable_snd)

/-- The digits are a measurable function of the indices; the heights are kept. -/
lemma measurable_digitsOfCoarse (n b j : ℕ) : Measurable (digitsOfCoarse n b j) :=
  measurable_fst.prodMk ((measurable_of_countable
    (fun g : Fin n → ℤ => fun i => digitsOfIdx b j (g i))).comp measurable_snd)

/-- "The first `j` digits of `U_i` determine the stage-`j` horizontal interval that contains
`U_i`", for all points at once: almost surely, the heights and the stage-`j` indices are the
function `coarseOfDigits` of the heights and the first `j` digits. -/
theorem coarseInfo_ae_eq_digitInfo {b : ℕ} (hb : 0 < b) (n j : ℕ) :
    coarseInfo n (b ^ j) =ᵐ[unifPts n] coarseOfDigits n b j ∘ digitInfo n b j := by
  -- the digits determine the indices, on the probability-one event of Section 2.1
  filter_upwards [ae_inUnit n, ae_noGrid n b] with P hP hgrid
  exact Prod.ext rfl (funext fun i =>
    gridIndex_eq_idxOfDigits hb j (hP i).1 fun m r => (hgrid i m r).1)

/-- Conversely, the stage-`j` intervals determine the first `j` digits: almost surely, the
heights and the first `j` digits are the function `digitsOfCoarse` of the heights and the
stage-`j` indices. -/
theorem digitInfo_ae_eq_coarseInfo {b : ℕ} (hb : 0 < b) (n j : ℕ) :
    digitInfo n b j =ᵐ[unifPts n] digitsOfCoarse n b j ∘ coarseInfo n (b ^ j) := by
  -- the indices determine the digits, on the probability-one event of Section 2.1
  filter_upwards [ae_inUnit n, ae_noGrid n b] with P hP hgrid
  exact Prod.ext rfl (funext fun i => funext fun k =>
    digit_eq_digitsOfIdx hb j (hP i).1.1 (fun m r => (hgrid i m r).1) k)

/-- **The two descriptions of `𝓕_j` give the same conditional expectations**, almost surely:
the σ-field generated by the heights and the first `j` digits, and the σ-field generated by
the heights and the stage-`j` indices. -/
theorem condExp_digitSigma {b : ℕ} (hb : 0 < b) (j : ℕ) (f : (Fin n → ℝ × ℝ) → ℝ) :
    (unifPts n)[f | digitSigma n b j] =ᵐ[unifPts n] (unifPts n)[f | stageSigma n b j] :=
  -- almost surely, the indices are a measurable function of the digits and the digits are a
  -- measurable function of the indices; the heights are kept
  condExp_comap_congr_ae (measurable_digitInfo n b j) (measurable_coarseInfo n (b ^ j))
    (measurable_coarseOfDigits n b j) (measurable_digitsOfCoarse n b j)
    (coarseInfo_ae_eq_digitInfo hb n j) (digitInfo_ae_eq_coarseInfo hb n j) f

/-- **Lemma 2.4** with `𝓕_j` generated by all heights and by the first `j` base-`b` digits of
every horizontal coordinate. -/
theorem lemma_2_4_digits {b h j : ℕ} (hb : 2 ≤ b) (hj : j < h) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, delta b h j P ≤
      ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P := by
  have hb0 : 0 < b := by omega
  -- Lemma 2.4 for the stage-`j` indices; the conditional expectation is almost surely the same
  filter_upwards [lemma_2_4 hb hj χ, condExp_digitSigma hb0 j
    (fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P)] with P hP hdig
  exact hP.trans_eq hdig.symm

/-- The fluctuation term `T` of display (10), with `𝓕_j` generated by the heights and the
first `j` digits. -/
def fluctDigits (χ : Fin n → ℤˣ) (b h : ℕ) (P : Fin n → ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range h,
    (Zpot χ b h (j + 1) P - ((unifPts n)[Zpot χ b h (j + 1) | digitSigma n b j]) P)

/-- Almost surely, the two versions of the fluctuation term agree. -/
theorem fluctDigits_ae_eq {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) :
    fluctDigits χ b h =ᵐ[unifPts n] fluct χ b h := by
  -- almost surely, the conditional expectations of all `h` transitions agree
  have hall : ∀ᵐ P ∂unifPts n, ∀ j ∈ Finset.range h,
      ((unifPts n)[Zpot χ b h (j + 1) | digitSigma n b j]) P =
        ((unifPts n)[Zpot χ b h (j + 1) | stageSigma n b j]) P :=
    (ae_ball_iff (Finset.range h).countable_toSet).mpr fun j _ =>
      condExp_digitSigma hb j (Zpot χ b h (j + 1))
  filter_upwards [hall] with P hP
  unfold fluctDigits fluct
  exact Finset.sum_congr rfl fun j hj => by rw [hP j hj]

/-- **Lemma 2.6** with `𝓕_j` generated by all heights and by the first `j` base-`b` digits of
every horizontal coordinate. -/
theorem lemma_2_6_digits {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) {lam : ℝ}
    (hlam : 0 < lam) :
    (unifPts n).real {P | fluctDigits χ b h P ≤ -lam} ≤
      Real.exp (-(lam ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n))) := by
  -- the events for the two versions of the fluctuation term differ by a null set
  have hsets : {P | fluctDigits χ b h P ≤ -lam} =ᵐ[unifPts n] {P | fluct χ b h P ≤ -lam} := by
    filter_upwards [fluctDigits_ae_eq hb h χ] with P hP
    show (fluctDigits χ b h P ≤ -lam) = (fluct χ b h P ≤ -lam)
    rw [hP]
  rw [measureReal_congr hsets]
  exact lemma_2_6 hb h χ hlam

/-! ### Display (10), "`Z_j` is `𝓕_j`-measurable", and the next digits -/

/-- **Display (10)** with `𝓕_j` generated by all heights and the first `j` digits. -/
theorem roadmap_digits {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, Zpot χ b h h P = Zpot χ b h 0 P +
      ∑ j ∈ Finset.range h,
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P +
      fluctDigits χ b h P := by
  -- almost surely, the conditional gains of all `h` transitions agree
  have hall : ∀ᵐ P ∂unifPts n, ∀ j ∈ Finset.range h,
      ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P =
        ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | stageSigma n b j]) P :=
    (ae_ball_iff (Finset.range h).countable_toSet).mpr fun j _ =>
      condExp_digitSigma hb j fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P
  -- display (10) for the stage-`j` indices; the fluctuation terms agree almost surely
  filter_upwards [roadmap hb h χ, hall, fluctDigits_ae_eq hb h χ] with P hP hgain hfluct
  rw [Finset.sum_congr rfl hgain, hfluct]
  exact hP

end

end R56Audit
end

section
/-!
# Proposition 2.7 of the manuscript, by the manuscript's proof

Auditor's supplement (not part of the audited archive).

**Proposition 2.7.** If `M ≤ n`, then

`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ (h / (64 b^{3/2})) √(n/M)] ≤ h (48/b)^{n/2} + 2ⁿ e^{-hM/(2048 b³)}`.

Here `M = b^(h-1)`. The proof of the manuscript, sentence by sentence:

* "Fix a coloring. Suppose that `G` holds and `‖F‖∞ ≤ hδ_*/8`." The coloring is `χ`. The event
  `G` that all `h` transitions are good is `∀ j < h, GoodTransition b h j P`, and
  `‖F‖∞ ≤ hδ_*/8` is `supNorm χ P ≤ h * deltaStar n b h / 8`.
* `condGain_ge_deltaStar`: "On `G`, every conditional gain is almost surely at least `δ_*`, by
  Lemmas 2.4 and 2.5."
* `Zpot_ge_of_good`: "So (10) and `Z_0 ≥ 0` give `Z_h ≥ hδ_* + T`."
* `Zpot_le_of_small`: "Also `Z_h ≤ hδ_*/4` by (9)."
* `fluct_le_of_good`: "Hence `T ≤ -3hδ_*/4`, and in particular `T ≤ -λ` for `λ = hδ_*/4`."
  The statement is `T ≤ -3hδ_*/4`; the proof of `good_inter_small_le` draws `T ≤ -λ` from it.
* `exponent_eq`: "Since `δ_*² = n/(64b³M)` by (12), the exponent in (13) is then
  `λ²M²/(2hn) = hδ_*²M²/(32n) = hM/(2048b³)`".
* `good_inter_small_le`: "We do not optimize the constants, and apply Lemma 2.6 with this
  `λ`. \[…\] and therefore `Pr[G and ‖F‖∞ ≤ hδ_*/8] ≤ exp(-hM/(2048b³))`."
* `prob_exists_small_le`: "The event `G` does not depend on the coloring. So we bound the
  probability of `G^c` once, by Lemma 2.5, and take a union bound over the colorings only for
  the other event:
  `Pr[∃χ: ‖F_χ‖∞ ≤ hδ_*/8] ≤ Pr(G^c) + Σ_{χ ∈ {±1}ⁿ} Pr[G and ‖F_χ‖∞ ≤ hδ_*/8]`."
* `threshold_eq`, `proposition_2_7`: "Since `hδ_*/8 = h√(n/M)/(64b^{3/2})`, this gives (14)."

**The σ-fields.** The proof uses the σ-fields `digitSigma n b j`, generated by all heights and
by the first `j` base-`b` digits of every horizontal coordinate, and the fluctuation term
`fluctDigits`: these are the manuscript's `𝓕_j` and `T`. They enter through the
manuscript-literal statements of `Digits.lean`: display (10) is `roadmap_digits`, Lemma 2.4 is
`lemma_2_4_digits`, and Lemma 2.6 is `lemma_2_6_digits`. (`Digits.lean` derives these three
statements from `roadmap`, `lemma_2_4` and `lemma_2_6`, which are about the σ-fields
`stageSigma` of the stage-`j` indices and the fluctuation term `fluct`; conditional
expectations given the two σ-fields agree almost surely, by `condExp_digitSigma`. Neither
`stageSigma` nor `fluct` occurs in the statements and proofs of this file.)

Everything here is about the potential `Z_j` of display (1) with heights in the continuum,
the σ-fields `𝓕_j`, and the fluctuation term `T`; the archive's finite-probe potential is
not used. The event of the proposition is stated with `‖F_χ‖∞` and the law `unifPts` of the
points; the archive's point-set interface (`badSet`, `threshold`) is not used, and
`ArchiveInterface.lean` is not imported. The only name of the archive that occurs in this file
is the law `unifPts` (used with the archive's instance that it is a probability measure), as
the `open` lines below show.

The archive's own proofs of display (14) are restated elsewhere: `proposition_2_7_archive` in
`ArchiveRoute.lean` (even `b` or `b ≤ 48`) and `proposition_2_7_probe` in `AllBases.lean` (the
finite-probe route for every `b ≥ 3`).
-/

namespace R56Audit

open MeasureTheory
open Riesz.PointSets (unifPts)

noncomputable section

variable {n : ℕ}

/-- `δ_* > 0` when there is at least one point. -/
lemma deltaStar_pos {b : ℕ} (hn : 0 < n) (hb : 0 < b) (h : ℕ) : 0 < deltaStar n b h := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold deltaStar
  have : 0 < Real.sqrt ((n : ℝ) / (b : ℝ) ^ (h - 1)) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- `δ_*² = n / (64 b³ M)`. -/
lemma deltaStar_sq {b : ℕ} (hb : 0 < b) (n h : ℕ) :
    deltaStar n b h ^ 2 = n / (64 * (b : ℝ) ^ 3 * (b : ℝ) ^ (h - 1)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : (0 : ℝ) ≤ n / (b : ℝ) ^ (h - 1) := by positivity
  unfold deltaStar
  rw [mul_pow, Real.sq_sqrt hq, rpow_three_halves_eq_mul_sqrt hbR.le, div_pow, mul_pow, mul_pow,
    Real.sq_sqrt hbR.le]
  field_simp
  ring

/-! ### A fixed coloring: `G` and `‖F‖∞ ≤ hδ_*/8` force `T ≤ -3hδ_*/4` -/

/-- "On `G`, every conditional gain is almost surely at least `δ_*`, by Lemmas 2.4 and 2.5."

The conditional gain of the transition `j → j+1` is `E[Z_{j+1} - Z_j | 𝓕_j]`, where `𝓕_j` is
the σ-field `digitSigma n b j` generated by all heights and by the first `j` base-`b` digits
of every horizontal coordinate, and `δ_*` is `deltaStar n b h`, display (12). `G` is the event
that all `h` transitions are good. The statement is for each transition separately: almost
surely, for every `j < h`, if the transition `j → j+1` is good (the event `G_j`), then its
conditional gain is at least `δ_*`. Lemma 2.4 is `lemma_2_4_digits`, and Lemma 2.5(i) is
`lemma_2_5_i`. -/
theorem condGain_ge_deltaStar {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, ∀ j < h, GoodTransition b h j P → deltaStar n b h ≤
      ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P := by
  have hb0 : 0 < b := by omega
  -- there are finitely many transitions, so it suffices to treat each transition `j → j+1`
  refine (ae_ball_iff (Set.to_countable (Set.Iio h))).mpr fun j hj => ?_
  -- Lemma 2.4: almost surely, its conditional gain is at least `δ_j`
  filter_upwards [lemma_2_4_digits hb hj χ] with P hP hG
  -- Lemma 2.5(i): on `G_j`, `δ_j ≥ δ_*`
  exact (lemma_2_5_i hn hb0 P hG).trans hP

/-- "So (10) and `Z_0 ≥ 0` give `Z_h ≥ hδ_* + T`."

Almost surely, on `G`, the event that all `h` transitions are good. Here `T` is the
fluctuation term `fluctDigits χ b h` of display (10), for the σ-fields `𝓕_j = digitSigma n b j`
generated by all heights and by the first `j` base-`b` digits of every horizontal coordinate.
Display (10) is `roadmap_digits`, and `Z_0 ≥ 0` is `Zpot_nonneg`. -/
theorem Zpot_ge_of_good {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, (∀ j < h, GoodTransition b h j P) →
      h * deltaStar n b h + fluctDigits χ b h P ≤ Zpot χ b h h P := by
  have hb0 : 0 < b := by omega
  filter_upwards [roadmap_digits hb0 h χ, condGain_ge_deltaStar hb h hn χ] with P hroad hgain hG
  -- on `G`, the `h` conditional gains add up to at least `hδ_*`
  have hsum : (h : ℝ) * deltaStar n b h ≤ ∑ j ∈ Finset.range h,
      ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P :=
    calc (h : ℝ) * deltaStar n b h = ∑ _j ∈ Finset.range h, deltaStar n b h := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range h,
          ((unifPts n)[fun P => Zpot χ b h (j + 1) P - Zpot χ b h j P | digitSigma n b j]) P :=
        Finset.sum_le_sum fun j hj =>
          hgain j (Finset.mem_range.mp hj) (hG j (Finset.mem_range.mp hj))
  -- display (10), and `Z_0 ≥ 0`
  have h0 := Zpot_nonneg hb0 χ h 0 P
  linarith

/-- "Also `Z_h ≤ hδ_*/4` by (9)."

This is under the assumption `‖F‖∞ ≤ hδ_*/8` of the proof; the bound of (9) that is used is
`Z_h ≤ 2‖F‖∞` (`Zpot_le_two_supNorm`). It holds for every position of the points. -/
theorem Zpot_le_of_small {b : ℕ} (hb : 0 < b) (h : ℕ) (χ : Fin n → ℤˣ) (P : Fin n → ℝ × ℝ)
    (hsmall : supNorm χ P ≤ h * deltaStar n b h / 8) :
    Zpot χ b h h P ≤ h * deltaStar n b h / 4 := by
  -- (9): `Z_h ≤ 2‖F‖∞`
  have hZ := Zpot_le_two_supNorm hb (le_refl h) χ P
  linarith

/-- "Hence `T ≤ -3hδ_*/4`, and in particular `T ≤ -λ` for `λ = hδ_*/4`."

Almost surely: if `G` holds, that is, if all `h` transitions are good, and if
`‖F_χ‖∞ ≤ hδ_*/8`, then `T ≤ -3hδ_*/4`. Here `T` is the fluctuation term `fluctDigits χ b h`
of display (10), for the σ-fields `𝓕_j = digitSigma n b j` generated by all heights and by the
first `j` base-`b` digits of every horizontal coordinate. This is the first half of the
sentence; the second half, `T ≤ -λ`, is drawn from it in the proof of `good_inter_small_le`. -/
theorem fluct_le_of_good {b : ℕ} (hb : 2 ≤ b) (h : ℕ) (hn : 0 < n) (χ : Fin n → ℤˣ) :
    ∀ᵐ P ∂unifPts n, (∀ j < h, GoodTransition b h j P) →
      supNorm χ P ≤ h * deltaStar n b h / 8 →
      fluctDigits χ b h P ≤ -(3 * h * deltaStar n b h / 4) := by
  filter_upwards [Zpot_ge_of_good hb h hn χ] with P hge hG hsmall
  -- `Z_h ≥ hδ_* + T` and `Z_h ≤ hδ_*/4`
  have h1 := hge hG
  have h2 := Zpot_le_of_small (by omega : 0 < b) h χ P hsmall
  linarith

/-! ### A fixed coloring: Lemma 2.6 with `λ = hδ_*/4` -/

/-- The exponent display of the proof, for `λ = hδ_*/4` and `M = b^(h-1)`: "Since
`δ_*² = n/(64b³M)` by (12), the exponent in (13) is then
`λ²M²/(2hn) = hδ_*²M²/(32n) = hM/(2048b³)`". The two equalities are the two parts of the
statement; (12) is used in the second one (`deltaStar_sq`). -/
theorem exponent_eq {b : ℕ} (hb : 0 < b) {h : ℕ} (hh : 0 < h) (hn : 0 < n) :
    (h * deltaStar n b h / 4) ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (2 * h * n) =
        h * deltaStar n b h ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (32 * n) ∧
      h * deltaStar n b h ^ 2 * ((b : ℝ) ^ (h - 1)) ^ 2 / (32 * n) =
        h * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · -- `λ² = h²δ_*²/16`, and one factor `h` cancels
    field_simp
    ring
  · -- `δ_*² = n/(64b³M)`, by (12)
    rw [deltaStar_sq hb]
    field_simp
    ring

/-- "We do not optimize the constants, and apply Lemma 2.6 with this `λ`. \[…\] and therefore
`Pr[G and ‖F‖∞ ≤ hδ_*/8] ≤ exp(-hM/(2048b³))`."

For a fixed coloring `χ`. `G` is the event that all `h` transitions are good, `λ = hδ_*/4`,
and `M = b^(h-1)`. Lemma 2.6 is `lemma_2_6_digits`, for the fluctuation term
`T = fluctDigits χ b h` of the σ-fields `𝓕_j = digitSigma n b j`. The omitted part is the
exponent display (`exponent_eq`). -/
theorem good_inter_small_le {b h : ℕ} (hb : 2 ≤ b) (hh : 1 ≤ h) (hn : 0 < n) (χ : Fin n → ℤˣ) :
    (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
        {P | supNorm χ P ≤ h * deltaStar n b h / 8}) ≤
      Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
  have hb0 : 0 < b := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hδ : 0 < deltaStar n b h := deltaStar_pos hn hb0 h
  have hlam : 0 < (h : ℝ) * deltaStar n b h / 4 := by positivity
  -- "apply Lemma 2.6 with this `λ`", that is, with `λ = hδ_*/4`
  have hfl := lemma_2_6_digits hb0 h χ hlam
  -- "the exponent in (13) is then `λ²M²/(2hn) = hδ_*²M²/(32n) = hM/(2048b³)`"
  obtain ⟨hexp1, hexp2⟩ := exponent_eq hb0 hh hn
  rw [hexp1, hexp2] at hfl
  refine le_trans ?_ hfl
  -- almost surely, `G` and `‖F‖∞ ≤ hδ_*/8` imply `T ≤ -λ`
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [fluct_le_of_good hb h hn χ] with P hP hmem
  -- "Hence `T ≤ -3hδ_*/4`, and in particular `T ≤ -λ` for `λ = hδ_*/4`."
  -- The first inequality is `fluct_le_of_good`; the second one follows because `λ > 0`.
  have hT : fluctDigits χ b h P ≤ -(3 * h * deltaStar n b h / 4) := hP hmem.1 hmem.2
  have hle : -(3 * h * deltaStar n b h / 4) ≤ -(h * deltaStar n b h / 4) := by linarith
  exact hT.trans hle

/-! ### All colorings -/

/-- The number of colorings. -/
lemma card_colorings (n : ℕ) : Fintype.card (Fin n → ℤˣ) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_units_int]

/-- "Since `hδ_*/8 = h√(n/M)/(64b^{3/2})`, this gives (14)": the threshold `hδ_*/8` of the
proof is the threshold of display (14). Here `M = b^(h-1)`. -/
lemma threshold_eq (n b h : ℕ) :
    h * deltaStar n b h / 8 =
      (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1)) := by
  -- by the definition (12) of `δ_*`
  unfold deltaStar
  ring

/-- The union-bound display of the proof: "The event `G` does not depend on the coloring. So
we bound the probability of `G^c` once, by Lemma 2.5, and take a union bound over the
colorings only for the other event:
`Pr[∃χ: ‖F_χ‖∞ ≤ hδ_*/8] ≤ Pr(G^c) + Σ_{χ ∈ {±1}ⁿ} Pr[G and ‖F_χ‖∞ ≤ hδ_*/8]`."

`G` is the event that all `h` transitions are good, so `G^c` is the event that some transition
`j → j+1` with `j < h` is not good. That `G` does not depend on the coloring is visible in the
statement: `GoodTransition b h j P` does not mention `χ`. This statement is the display; the
bound for `Pr(G^c)` by Lemma 2.5 (`lemma_2_5_ii_all`) is inserted in `proposition_2_7`. -/
theorem prob_exists_small_le {b h : ℕ} :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ h * deltaStar n b h / 8} ≤
      (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} +
        ∑ χ : Fin n → ℤˣ, (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
          {P | supNorm χ P ≤ h * deltaStar n b h / 8}) := by
  -- either `G^c` holds, or `G` holds and some coloring has a small norm
  have hsub : {P : Fin n → ℝ × ℝ | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ h * deltaStar n b h / 8} ⊆
      {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ∪ ⋃ χ : Fin n → ℤˣ,
        ({P | ∀ j < h, GoodTransition b h j P} ∩
          {P | supNorm χ P ≤ h * deltaStar n b h / 8}) := by
    rintro P ⟨χ, hχ⟩
    by_cases hG : ∀ j < h, GoodTransition b h j P
    · exact Or.inr (Set.mem_iUnion.mpr ⟨χ, hG, hχ⟩)
    · push Not at hG
      exact Or.inl hG
  calc (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ h * deltaStar n b h / 8}
      ≤ (unifPts n).real ({P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} ∪
          ⋃ χ : Fin n → ℤˣ, ({P | ∀ j < h, GoodTransition b h j P} ∩
            {P | supNorm χ P ≤ h * deltaStar n b h / 8})) := measureReal_mono hsub
    _ ≤ (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} +
          (unifPts n).real (⋃ χ : Fin n → ℤˣ, ({P | ∀ j < h, GoodTransition b h j P} ∩
            {P | supNorm χ P ≤ h * deltaStar n b h / 8})) := measureReal_union_le _ _
    -- the union bound over the colorings, only for the other event
    _ ≤ (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} +
          ∑ χ : Fin n → ℤˣ, (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
            {P | supNorm χ P ≤ h * deltaStar n b h / 8}) :=
        add_le_add_right (measureReal_iUnion_fintype_le _) _

/-- **Proposition 2.7 (simultaneous probability bound)**, display (14), with `M = b^{h-1}`:
if `M ≤ n`, then

`Pr[∃ χ ∈ {±1}ⁿ : ‖F_χ‖∞ ≤ (h / (64 b^{3/2})) √(n/M)] ≤ h (48/b)^{n/2} + 2ⁿ e^{-hM/(2048 b³)}`,

for every integer base `b ≥ 3` and every `h ≥ 1`, by the proof of the manuscript: the
identity (10) for the potential of display (1), Lemmas 2.4, 2.5 and 2.6, and a union bound
over the colorings. The last step of the proof: "Since `hδ_*/8 = h√(n/M)/(64b^{3/2})`, this
gives (14)", where "this" is the union-bound display (`prob_exists_small_le`), with the bounds
for its terms (`lemma_2_5_ii_all`, `good_inter_small_le`) and the number `2ⁿ` of colorings
(`card_colorings`). The event is measurable (`measurableSet_exists_supNorm_le`). -/
theorem proposition_2_7 {n b h : ℕ} (hb : 3 ≤ b) (hh : 1 ≤ h) (hMn : b ^ (h - 1) ≤ n) :
    (unifPts n).real {P | ∃ χ : Fin n → ℤˣ,
        supNorm χ P ≤ (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} ≤
      h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
        2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hMn
  -- "Since `hδ_*/8 = h√(n/M)/(64b^{3/2})`, this gives (14)."
  rw [← threshold_eq n b h]
  -- the union-bound display
  calc (unifPts n).real {P | ∃ χ : Fin n → ℤˣ, supNorm χ P ≤ h * deltaStar n b h / 8}
      ≤ (unifPts n).real {P | ∃ j, j < h ∧ ¬ GoodTransition b h j P} +
          ∑ χ : Fin n → ℤˣ, (unifPts n).real ({P | ∀ j < h, GoodTransition b h j P} ∩
            {P | supNorm χ P ≤ h * deltaStar n b h / 8}) := prob_exists_small_le
    -- `Pr(G^c) ≤ h (48/b)^{n/2}` by Lemma 2.5, and the bound for each fixed coloring
    _ ≤ h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          ∑ _χ : Fin n → ℤˣ,
            Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) :=
        add_le_add (lemma_2_5_ii_all hb hMn)
          (Finset.sum_le_sum fun χ _ => good_inter_small_le (by omega) hh hn χ)
    -- there are `2ⁿ` colorings
    _ = h * (48 / (b : ℝ)) ^ ((n : ℝ) / 2) +
          2 ^ n * Real.exp (-((h : ℝ) * (b : ℝ) ^ (h - 1) / (2048 * (b : ℝ) ^ 3))) := by
        rw [Finset.sum_const, Finset.card_univ, card_colorings, nsmul_eq_mul]
        push_cast
        ring

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

open TusnadyPlane.Dev.Bridge in
theorem chk_proposition_2_7 (n b h : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b) (hh : 1 ≤ h)
    (hM : comparisonCount b h ≤ n) :
    (sampleLaw n).real {P | ∃ χ : Coloring n, discrepancy P χ ≤
      (h : ℝ)/(64*(b : ℝ)^(3/2 : ℝ)) * Real.sqrt ((n : ℝ)/comparisonCount b h)} ≤
      (h : ℝ)*(48/(b : ℝ))^((n : ℝ)/2) +
        (2 : ℝ)^n * Real.exp (-((h : ℝ)*comparisonCount b h/(2048*(b : ℝ)^3))) := by
  have hcm : (comparisonCount b h : ℝ) = (b : ℝ) ^ (h - 1) := by
    unfold comparisonCount; push_cast; rfl
  have hset : {P : Sample n | ∃ χ : Coloring n, discrepancy P χ ≤
      (h : ℝ)/(64*(b : ℝ)^(3/2 : ℝ)) * Real.sqrt ((n : ℝ)/comparisonCount b h)} =
      {P | ∃ χ : Fin n → ℤˣ, R56Audit.supNorm χ P ≤
        (h : ℝ) / (64 * (b : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (n / (b : ℝ) ^ (h - 1))} := by
    ext P
    simp only [Set.mem_setOf_eq, hcm]
    constructor
    · rintro ⟨χ, hχ⟩
      exact ⟨chiU χ, by rwa [discrepancy_eq] at hχ⟩
    · rintro ⟨χ', hχ'⟩
      obtain ⟨χ, rfl⟩ := chiU_surj χ'
      exact ⟨χ, by rwa [discrepancy_eq]⟩
  rw [hset, hcm, sampleLaw_eq]
  exact R56Audit.proposition_2_7 hb hh hM

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_proposition_2_7 := @TusnadyPlane.RandomPoints.chk_proposition_2_7
