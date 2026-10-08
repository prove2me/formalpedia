-- Prove2me | solution 1 for RadGauss.Structural.theorem_12_part_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:23:30.768126+00:00
-- url     : https://prove2.me/submissions/941d97e3-6531-4ac9-9736-6341ec72d21d

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

set_option autoImplicit false

lemma rg6623_iSup_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E)
    (φ : E → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    (⨆ g ∈ convexHull ℝ S, ENNReal.ofReal (φ g)) = ⨆ g ∈ S, ENNReal.ofReal (φ g) := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    obtain ⟨y, hyS, hy⟩ := hφ.exists_ge_of_mem_convexHull (Set.subset_univ S) hg
    exact le_trans (ENNReal.ofReal_le_ofReal hy) (le_iSup₂ (f := fun g _ => ENNReal.ofReal (φ g)) y hyS)
  · exact iSup₂_le fun g hg =>
      le_iSup₂ (f := fun g _ => ENNReal.ofReal (φ g)) g (subset_convexHull ℝ S hg)

lemma rg6623_convex {X : Type*} (n : ℕ) (c : ℝ) (s : Fin n → ℝ) (x : Fin n → X) :
    ConvexOn ℝ Set.univ (fun g : X → ℝ => |c * ∑ i, s i * g (x i)|) := by
  refine ⟨convex_univ, fun g _ h _ a b ha hb _ => ?_⟩
  have key : c * ∑ i, s i * ((a • g + b • h) (x i))
      = a * (c * ∑ i, s i * g (x i)) + b * (c * ∑ i, s i * h (x i)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring
  simp only [smul_eq_mul]
  rw [key]
  calc |a * (c * ∑ i, s i * g (x i)) + b * (c * ∑ i, s i * h (x i))|
      ≤ |a * (c * ∑ i, s i * g (x i))| + |b * (c * ∑ i, s i * h (x i))| := abs_add_le _ _
    _ = a * |c * ∑ i, s i * g (x i)| + b * |c * ∑ i, s i * h (x i)| := by
        rw [abs_mul a, abs_mul b, abs_of_nonneg ha, abs_of_nonneg hb]

lemma rg6623_emp_conv {X : Type*} (n : ℕ) (F : Set (X → ℝ)) (x : Fin n → X) :
    RadGauss.RiskBound.empiricalRademacher n (convexHull ℝ F) x
      = RadGauss.RiskBound.empiricalRademacher n F x := by
  unfold RadGauss.RiskBound.empiricalRademacher
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact rg6623_iSup_convexHull F _
    (rg6623_convex n (2 / (n : ℝ)) (fun i => RadGauss.RiskBound.signVal (σ i)) x)

lemma rg6623_iSup_neg {E : Type*} [InvolutiveNeg E] (S : Set E) (φ : E → ℝ≥0∞)
    (hφ : ∀ g, φ (-g) = φ g) : (⨆ g ∈ -S, φ g) = ⨆ g ∈ S, φ g := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [← hφ g]
    exact le_iSup₂ (f := fun g (_ : g ∈ S) => φ g) (-g) (Set.mem_neg.mp hg)
  · refine iSup₂_le fun g hg => ?_
    rw [← hφ g]
    exact le_iSup₂ (f := fun g (_ : g ∈ -S) => φ g) (-g) (Set.neg_mem_neg.mpr hg)

lemma rg6623_emp_neg {X : Type*} (n : ℕ) (F : Set (X → ℝ)) (x : Fin n → X) :
    RadGauss.RiskBound.empiricalRademacher n (F ∪ -F) x
      = RadGauss.RiskBound.empiricalRademacher n F x := by
  unfold RadGauss.RiskBound.empiricalRademacher
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iSup_union]
  refine (congrArg (_ ⊔ ·) (rg6623_iSup_neg F _ ?_)).trans (sup_idem _)
  intro g
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, abs_neg]

open MeasureTheory ENNReal Pointwise in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) :
    RadGauss.RiskBound.rademacherComplexity μ n F = RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) ∧
      RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) =
        RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ (F ∪ -F)) := by
  unfold RadGauss.RiskBound.rademacherComplexity
  constructor
  · congr 1
    funext x
    exact (rg6623_emp_conv n F x).symm
  · congr 1
    funext x
    rw [rg6623_emp_conv, rg6623_emp_conv, rg6623_emp_neg]
