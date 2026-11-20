-- Prove2me | solution 1 for TusnadyPlane.RandomPoints.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:46:37.996174+00:00
-- url     : https://prove2.me/submissions/48512397-d438-440b-93e5-31f0ba7f5101

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
end

section
namespace Oscillation
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The normalized average on a finite set. -/
def finAvg (f : α → ℝ) : ℝ := (∑ x, f x) / Fintype.card α

@[simp] lemma finAvg_const [Nonempty α] (c : ℝ) : finAvg (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finAvg, hc]

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

end Riesz

namespace Riesz

open PointSets

/-- Right-closed grid cells. The point zero lies in a separate null fiber
under the uniform measure on the unit interval. -/
noncomputable def gridIndex (n : ℕ) (x : ℝ) : ℤ := ⌈(n : ℝ) * x⌉ - 1

noncomputable abbrev gridSigma (n : ℕ) : MeasurableSpace ℝ :=
  (inferInstance : MeasurableSpace ℤ).comap (gridIndex n)

theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) := by
  exact ((measurable_const.mul measurable_id).ceil.sub_const 1)

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

/-- The information in the first `k` horizontal cells for every sample point. -/
def sampleGridIndex (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => gridIndex k (x i)

abbrev sampleGridSigma (n k : ℕ) : MeasurableSpace (Fin n → ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → ℤ)).comap (sampleGridIndex n k)

lemma measurable_sampleGridIndex (n k : ℕ) : Measurable (sampleGridIndex n k) := by
  exact measurable_pi_iff.mpr (fun i => (measurable_gridIndex k).comp (measurable_pi_apply i))


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

abbrev pointSampleLaw (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin n => μI.prod μI)

lemma pointSampleLaw_eq_unifPts (n : ℕ) : pointSampleLaw n = unifPts n := by
  unfold pointSampleLaw unifPts
  simp_rw [unitSq_eq]

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

/-! ### Elementary facts -/

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

/-! ### Blocks -/

/-! ### Lemma 2.1 -/

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

/-! ### Two moments -/

/-! ### From moments to the absolute value -/

end General

/-! ### Fact 2.2 -/

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

variable [MeasurableSingletonClass D]

end Uniform

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

/-! ### Sums of independent symmetric jumps -/

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

/-! ### The local experiment -/

/-! ### Step 1: averaging the children -/

/-! ### Step 2: the weights in `ā` -/

/-! ### Step 3: taking expectations -/

/-! ### Step 4: the gain

In the manuscript `D` is the sum of the jumps of the points of `R^in`, and `g` is `ā` without
these jumps. In the statements below a set `S` of points of `I` takes the place of the set of
the points of `R^in`: `D = jumpSum S (jump b ε) r` (`jumpSum` is defined in
`SymmetricSums.lean`) and `g = withoutJumps b ε V side S r`. -/

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

/-! ### Step 4: the last display

`E|mid_{B_b} ā - mid_{B_1} ā| ≥ σ √(m_R/3) = (√(b²-1) / (6b)) √(m_R) ≥ √(m_R) / 8`,

where `σ² = (b² - 1) / (12 b²)`. The first inequality is `expected_offset_ge_sigma`, the
equality is `sigma_mul_sqrt_eq`, the last inequality is `sqrt_sq_sub_one_div_ge`, and
`expected_offset_ge` is the inequality between the two ends of the display.
`sqrt_div_eight_le` is the equality and the last inequality together. -/

/-! ### Lemma 2.3 -/

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

/-! ### The extrema over an interval are extrema over finitely many heights -/

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

/-- The `v`-th vertical interval of stage `j`: `[v b^{j-h}, (v+1) b^{j-h})`, closed at the
bottom and open at the top. -/
def vcell (b h j v : ℕ) : Set ℝ := Set.Ico (v * vlen b h j) ((v + 1) * vlen b h j)

/-! ### The potential, as in the manuscript -/

/-! ### The potential, read from the heights and the cell indices -/

/-! ### Bounds: display (9) -/

/-! ### Measurability -/

/-! ### The next digit -/

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

/-!
### Proof of the conditional law

For fixed heights, only the horizontal coordinates are integrated, and the archive's theorem
for the horizontal coordinates applies (`integral_fresh_eq_integral_finAvg`). Integrating
over the heights gives the statement in integrated form (`integral_fresh_given_heights`).
Applied to the function cut off outside an event of the conditioning σ-algebra, this is the
characterization of the conditional expectation.
-/

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

/-! ### The potential as a process -/

/-! ### The next digits -/

/-! ### The conditional expectation of the next potential -/

/-! ### The potential of the manuscript -/

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

/-! ### Conditional expectations of the potential -/

/-! ### Lemma 2.4 -/

/-! ### The fluctuation term and display (10) -/

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

/-! ### The cells of one horizontal interval -/

/-! ### The potential -/

/-! ### The next digit -/

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

/-! ### One difference -/

/-! ### One difference, as the manuscript states it

The manuscript states the step for a σ-field `𝓗`: "Let `𝓗` be a σ-field, and let
`E[Y | 𝓗] = 0` and `|Y| ≤ c`." The next two theorems have this form. They are stand-alone
statements of the manuscript's lemma: the proof of `fact_A_1` in this file works with product
measures and does not need them. -/

/-! ### Bounded differences for a product of probability measures -/

/-! ### Conditioning on an independent random element -/

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

/-! ### Markov's inequality -/

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

/-! ### Step 3: all transitions -/

/-! ### The displays of Steps 2 and 3 in the manuscript's terms -/

/-! ### Lemma 2.6 -/

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

/-! ### Display (10), "`Z_j` is `𝓕_j`-measurable", and the next digits -/

end

end R56Audit
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.Bridge

open TusnadyPlane.RandomPoints

end TusnadyPlane.Dev.Bridge
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.Bridge

open TusnadyPlane.RandomPoints

theorem vlo_eq {b : ℕ} (hb : 0 < b) {h j : ℕ} (hj : j < h) (l : ℕ) :
    gridLo b (h - j - 1) l + 1 / (b : ℝ) ^ (h - j) =
      (((l : ℝ) * (b : ℝ) ^ (j + 1) + (b : ℝ) ^ j) / (b : ℝ) ^ h) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have e1 : j + t + 1 - j - 1 = t := by omega
  have e2 : j + t + 1 - j = t + 1 := by omega
  unfold gridLo
  rw [e1, e2]
  field_simp
  ring

theorem vhi_eq {b : ℕ} (hb : 0 < b) {h j : ℕ} (hj : j < h) (l : ℕ) :
    gridHi b (h - j - 1) l - 1 / (b : ℝ) ^ (h - j) =
      ((((l : ℝ) + 1) * (b : ℝ) ^ (j + 1) - (b : ℝ) ^ j) / (b : ℝ) ^ h) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have e1 : j + t + 1 - j - 1 = t := by omega
  have e2 : j + t + 1 - j = t + 1 := by omega
  unfold gridHi
  rw [e1, e2]
  field_simp
  ring

theorem mem_inner_iff {n b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Sample n}
    (hng : R56Audit.NoGrid b P) (i : Fin n) (k l : ℕ) :
    P i ∈ innerRegion b h j k l ↔ P i ∈ R56Audit.innerRegion b h j k l := by
  unfold innerRegion R56Audit.innerRegion
  rw [vlo_eq hb hj, vhi_eq hb hj]
  simp only [Set.prod, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Icc, Set.mem_prod, gridLo, gridHi]
  have hne : (P i).1 ≠ (((k + 1 : ℤ)) : ℝ) / (b : ℝ) ^ j := (hng i (k + 1) j).1
  push_cast at hne
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.le⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, lt_of_le_of_ne h2 hne⟩, h3⟩

theorem innerCount_eq {n b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Sample n}
    (hng : R56Audit.NoGrid b P) (k l : ℕ) :
    innerCount b h j k l P = R56Audit.innerCount b h j P k l := by
  classical
  unfold innerCount R56Audit.innerCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_inner_iff hb hj hng i k l

theorem delta_eq {n b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Sample n}
    (hng : R56Audit.NoGrid b P) :
    delta b h j P = R56Audit.delta b h j P := by
  unfold delta R56Audit.delta
  rw [one_div, inv_mul_eq_div]
  have hM : (comparisonCount b h : ℝ) = (b : ℝ) ^ (h - 1) := by
    unfold comparisonCount; push_cast; rfl
  rw [hM]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [innerCount_eq hb hj hng]

theorem deltaStar_eq (n b h : ℕ) : deltaStar n b h = R56Audit.deltaStar n b h := by
  unfold deltaStar R56Audit.deltaStar comparisonCount
  push_cast
  rfl

end TusnadyPlane.Dev.Bridge
end

section
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.Dev.Bridge

open TusnadyPlane.RandomPoints

theorem cell_unique {B : ℝ} (hB : 0 < B) {k k' : ℕ} {x : ℝ}
    (h1 : x ∈ Set.Ico ((k : ℝ) / B) (((k : ℝ) + 1) / B))
    (h2 : x ∈ Set.Ico ((k' : ℝ) / B) (((k' : ℝ) + 1) / B)) : k = k' := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  have c1 : (k : ℝ) < (k' : ℝ) + 1 := (div_lt_div_iff_of_pos_right hB).mp (lt_of_le_of_lt a1 b2)
  have c2 : (k' : ℝ) < (k : ℝ) + 1 := (div_lt_div_iff_of_pos_right hB).mp (lt_of_le_of_lt b1 a2)
  have d1 : k < k' + 1 := by exact_mod_cast c1
  have d2 : k' < k + 1 := by exact_mod_cast c2
  omega

theorem region_unique {b h j : ℕ} (hb : 0 < b) (hj : j < h) {z : ℝ × ℝ} {k l k' l' : ℕ}
    (h1 : z ∈ innerRegion b h j k l) (h2 : z ∈ innerRegion b h j k' l') : k = k' ∧ l = l' := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold innerRegion at h1 h2
  simp only [Set.prod, Set.mem_Ico, Set.mem_setOf_eq] at h1 h2
  have hp : (0 : ℝ) < 1 / (b : ℝ) ^ (h - j) := by positivity
  refine ⟨cell_unique (B := (b : ℝ) ^ j) (x := z.1) (by positivity) h1.1 h2.1,
    cell_unique (B := (b : ℝ) ^ (h - j - 1)) (x := z.2) (by positivity) ⟨?_, ?_⟩ ⟨?_, ?_⟩⟩
  · have := h1.2.1; unfold gridLo at this; linarith
  · have := h1.2.2; unfold gridHi at this; linarith
  · have := h2.2.1; unfold gridLo at this; linarith
  · have := h2.2.2; unfold gridHi at this; linarith

theorem goodTransition_iff {n b h j : ℕ} (hb : 0 < b) (hj : j < h) {P : Sample n}
    (hng : R56Audit.NoGrid b P) :
    P ∈ GoodTransition n b h j ↔ R56Audit.GoodTransition b h j P := by
  classical
  have hM : (comparisonCount b h : ℝ) = (b : ℝ) ^ (h - 1) := by
    unfold comparisonCount; push_cast; rfl
  -- the two sums
  have key : (∑ k : Fin (b ^ j), ∑ l : Fin (b ^ (h - j - 1)),
      let m := innerCount b h j k.val l.val P
      if (m : ℝ) ≤ (b : ℝ) * n / comparisonCount b h then (m : ℝ) else 0) =
      ((Finset.univ.filter (fun i => ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
        P i ∈ R56Audit.innerRegion b h j c v ∧ ¬ R56Audit.Heavy b h j P c v)).card : ℝ) := by
    rw [hM]
    simp only [innerCount_eq hb hj hng]
    rw [← Fintype.sum_prod_type']
    -- per point, at most one region contains it
    set g : Fin n → (Fin (b ^ j) × Fin (b ^ (h - j - 1))) → Prop := fun i p =>
      ¬ R56Audit.Heavy b h j P p.1 p.2 ∧ P i ∈ innerRegion b h j p.1.val p.2.val with hg
    have hone : ∀ i, (∑ p : Fin (b ^ j) × Fin (b ^ (h - j - 1)), if g i p then (1 : ℝ) else 0) =
        if (∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
          P i ∈ R56Audit.innerRegion b h j c v ∧ ¬ R56Audit.Heavy b h j P c v) then 1 else 0 := by
      intro i
      rw [Finset.sum_boole]
      by_cases hex : ∃ c : Fin (b ^ j), ∃ v : Fin (b ^ (h - j - 1)),
          P i ∈ R56Audit.innerRegion b h j c v ∧ ¬ R56Audit.Heavy b h j P c v
      · rw [if_pos hex]
        obtain ⟨c, v, hcv, hhv⟩ := hex
        have hcv' : P i ∈ innerRegion b h j c.val v.val := (mem_inner_iff hb hj hng i _ _).mpr hcv
        have : Finset.univ.filter (fun p => g i p) = {(c, v)} := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hg]
          constructor
          · rintro ⟨hp1, hp2⟩
            obtain ⟨e1, e2⟩ := region_unique hb hj hp2 hcv'
            exact Prod.ext (Fin.ext e1) (Fin.ext e2)
          · rintro rfl
            exact ⟨hhv, hcv'⟩
        rw [this]; simp
      · rw [if_neg hex]
        have : Finset.univ.filter (fun p => g i p) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, hg]
          rintro ⟨hp1, hp2⟩
          exact hex ⟨p.1, p.2, (mem_inner_iff hb hj hng i _ _).mp hp2, hp1⟩
        rw [this]; simp
    rw [Finset.card_filter]
    push_cast
    simp_rw [← hone]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_boole]
    have hc : R56Audit.innerCount b h j P p.1 p.2 =
        (Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1.val p.2.val)).card := by
      rw [← innerCount_eq hb hj hng]
      unfold innerCount
      congr 1
    by_cases hH : R56Audit.Heavy b h j P p.1 p.2
    · have hlt : (b : ℝ) * n / (b : ℝ) ^ (h - 1) < (R56Audit.innerCount b h j P p.1 p.2 : ℝ) := hH
      rw [if_neg (not_le.mpr hlt)]
      have : Finset.univ.filter (fun i => g i p) = ∅ := by
        ext i
        simp [hg, hH]
      rw [this]; simp
    · have hle : (R56Audit.innerCount b h j P p.1 p.2 : ℝ) ≤ (b : ℝ) * n / (b : ℝ) ^ (h - 1) :=
        not_lt.mp hH
      rw [if_pos hle]
      have : Finset.univ.filter (fun i => g i p) =
          Finset.univ.filter (fun i => P i ∈ innerRegion b h j p.1.val p.2.val) := by
        ext i
        simp [hg, hH]
      rw [this, hc]
  unfold GoodTransition R56Audit.GoodTransition
  show (n : ℝ) / 2 ≤ _ ↔ (n : ℝ) / 2 ≤ _
  rw [key]

end TusnadyPlane.Dev.Bridge
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
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

open TusnadyPlane.Dev.Bridge in
theorem chk_lemma_2_5 (n b h j : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b)
    (hh : 1 ≤ h) (hj : j < h) :
    (∀ᵐ P ∂sampleLaw n, P ∈ GoodTransition n b h j → deltaStar n b h ≤ delta b h j P) ∧
    (comparisonCount b h ≤ n →
      (sampleLaw n).real (GoodTransition n b h j)ᶜ ≤ (48/(b : ℝ))^((n : ℝ)/2) ∧
      (sampleLaw n).real (AllGood n b h)ᶜ ≤ (h : ℝ)*(48/(b : ℝ))^((n : ℝ)/2)) := by
  have hb0 : 0 < b := by omega
  rw [sampleLaw_eq]
  refine ⟨?_, fun hM => ?_⟩
  · filter_upwards [R56Audit.ae_noGrid n b] with P hng hG
    rw [deltaStar_eq, delta_eq hb0 hj hng]
    exact R56Audit.lemma_2_5_i (by omega) hb0 P ((goodTransition_iff hb0 hj hng).mp hG)
  · have hMn : b ^ (h - 1) ≤ n := hM
    refine ⟨?_, ?_⟩
    · have hset : (GoodTransition n b h j)ᶜ =ᵐ[Riesz.PointSets.unifPts n]
          {P | ¬ R56Audit.GoodTransition b h j P} := by
        filter_upwards [R56Audit.ae_noGrid n b] with P hng
        apply propext
        show P ∉ GoodTransition n b h j ↔ ¬ R56Audit.GoodTransition b h j P
        rw [goodTransition_iff hb0 hj hng]
      exact (measureReal_congr hset).le.trans (R56Audit.lemma_2_5_ii hb hMn hj)
    · have hset : (AllGood n b h)ᶜ =ᵐ[Riesz.PointSets.unifPts n]
          {P | ∃ j, j < h ∧ ¬ R56Audit.GoodTransition b h j P} := by
        filter_upwards [R56Audit.ae_noGrid n b] with P hng
        apply propext
        show P ∉ AllGood n b h ↔ ∃ j, j < h ∧ ¬ R56Audit.GoodTransition b h j P
        unfold AllGood
        simp only [Set.mem_setOf_eq, not_forall]
        constructor
        · rintro ⟨j', hj', hn'⟩
          exact ⟨j', hj', fun hG => hn' ((goodTransition_iff hb0 hj' hng).mpr hG)⟩
        · rintro ⟨j', hj', hn'⟩
          exact ⟨j', hj', fun hG => hn' ((goodTransition_iff hb0 hj' hng).mp hG)⟩
      exact (measureReal_congr hset).le.trans (R56Audit.lemma_2_5_ii_all hb hMn)

end TusnadyPlane.RandomPoints
end

theorem solution : type_of% @TusnadyPlane.RandomPoints.chk_lemma_2_5 := @TusnadyPlane.RandomPoints.chk_lemma_2_5
