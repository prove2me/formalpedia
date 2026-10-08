-- Prove2me | solution 1 for RadGauss.Discrepancy.discrepancy_union_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:05:08.717538+00:00
-- url     : https://prove2.me/submissions/766df543-a74e-4304-a3de-2d29a9afee1a

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- The involution of `Fin (2m)` exchanging the two halves. -/
def swapFun (m : ℕ) (i : Fin (2 * m)) : Fin (2 * m) :=
  if h : i.val < m then ⟨i.val + m, by omega⟩ else ⟨i.val - m, by omega⟩

lemma swapFun_val (m : ℕ) (i : Fin (2 * m)) :
    (swapFun m i).val = if i.val < m then i.val + m else i.val - m := by
  unfold swapFun; split_ifs <;> rfl

lemma swapFun_invol (m : ℕ) : Function.Involutive (swapFun m) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  rw [swapFun_val, swapFun_val]
  split_ifs <;> omega

lemma swapFun_lt (m : ℕ) (i : Fin (2 * m)) : (swapFun m i).val < m ↔ ¬ i.val < m := by
  rw [swapFun_val]; have hi := i.isLt; split_ifs <;> omega

/-- The halves-swapping permutation. -/
def tau (m : ℕ) : Equiv.Perm (Fin (2 * m)) := (swapFun_invol m).toPerm _

lemma sum_swap (m : ℕ) (g : Fin (2 * m) → ℝ) : ∑ i, g (swapFun m i) = ∑ i, g i :=
  Equiv.sum_comp (tau m) g

lemma halfDiff_swap {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) :
    halfDiff m f (fun i => x (swapFun m i)) = - halfDiff m f x := by
  unfold halfDiff
  have h1 : ∑ i : Fin (2 * m), (if i.val < m then f (x (swapFun m i)) else 0)
      = ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x i)) := by
    calc ∑ i : Fin (2 * m), (if i.val < m then f (x (swapFun m i)) else 0)
        = ∑ i : Fin (2 * m), (fun j : Fin (2 * m) => if j.val < m then 0 else f (x j))
            (swapFun m i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [swapFun_lt]
          split_ifs <;> simp_all
      _ = _ := sum_swap m (fun j : Fin (2 * m) => if j.val < m then 0 else f (x j))
  have h2 : ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x (swapFun m i)))
      = ∑ i : Fin (2 * m), (if i.val < m then f (x i) else 0) := by
    calc ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x (swapFun m i)))
        = ∑ i : Fin (2 * m), (fun j : Fin (2 * m) => if j.val < m then f (x j) else 0)
            (swapFun m i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [swapFun_lt]
          split_ifs <;> simp_all
      _ = _ := sum_swap m (fun j : Fin (2 * m) => if j.val < m then f (x j) else 0)
  rw [h1, h2]; ring

lemma halfDiff_eq {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) :
    halfDiff m f x = (2 / ((2 * m : ℕ) : ℝ)) *
      ∑ i : Fin (2 * m), RadGauss.RiskBound.signVal (decide (i.val < m)) * f (x i) := by
  unfold halfDiff
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.val < m <;> simp [h, RadGauss.RiskBound.signVal]

lemma neg_halfDiff_eq {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) :
    - halfDiff m f x = (2 / ((2 * m : ℕ) : ℝ)) *
      ∑ i : Fin (2 * m), RadGauss.RiskBound.signVal (decide ¬ (i.val < m)) * f (x i) := by
  rw [halfDiff_eq, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.val < m <;> simp [h, RadGauss.RiskBound.signVal]

lemma halfDiff_neg {X : Type*} (m : ℕ) (f : X → ℝ) (x : Fin (2 * m) → X) :
    halfDiff m (-f) x = - halfDiff m f x := by
  rw [halfDiff_eq, halfDiff_eq, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_neg]

lemma abs_sum_le_card {m : ℕ} (g : Fin (2 * m) → ℝ) (hg : ∀ i, |g i| ≤ 1) :
    |∑ i, g i| ≤ ((2 * m : ℕ) : ℝ) := by
  calc |∑ i, g i| ≤ ∑ i, |g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (2 * m), (1 : ℝ) := Finset.sum_le_sum fun i _ => hg i
    _ = ((2 * m : ℕ) : ℝ) := by simp

lemma halfDiff_abs_le {X : Type*} (m : ℕ) (hm : 0 < m) (f : X → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (x : Fin (2 * m) → X) : |halfDiff m f x| ≤ 4 := by
  unfold halfDiff
  set c : ℝ := 2 / ((2 * m : ℕ) : ℝ) with hcdef
  set N : ℝ := ((2 * m : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hcN : c * N = 2 := by rw [hcdef]; field_simp
  have hfa : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr (hf y)
  have e1 : |∑ i : Fin (2 * m), (if i.val < m then f (x i) else 0)| ≤ N :=
    abs_sum_le_card _ fun i => by split_ifs <;> simp [hfa]
  have e2 : |∑ i : Fin (2 * m), (if i.val < m then 0 else f (x i))| ≤ N :=
    abs_sum_le_card _ fun i => by split_ifs <;> simp [hfa]
  have k1 : |c * ∑ i : Fin (2 * m), (if i.val < m then f (x i) else 0)| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg hc0, ← hcN]; exact mul_le_mul_of_nonneg_left e1 hc0
  have k2 : |c * ∑ i : Fin (2 * m), (if i.val < m then 0 else f (x i))| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg hc0, ← hcN]; exact mul_le_mul_of_nonneg_left e2 hc0
  have := abs_le.mp k1
  have := abs_le.mp k2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma bdd {X : Type*} (m : ℕ) (hm : 0 < m) (G : Set (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (x : Fin (2 * m) → X) :
    BddAbove (Set.range fun g : G => halfDiff m (g : X → ℝ) x) :=
  ⟨4, by
    rintro _ ⟨g, rfl⟩
    exact (abs_le.mp (halfDiff_abs_le m hm g (hG g g.2) x)).2⟩

lemma bddNeg {X : Type*} (m : ℕ) (hm : 0 < m) (G : Set (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (x : Fin (2 * m) → X) :
    BddAbove (Set.range fun g : G => - halfDiff m (g : X → ℝ) x) :=
  ⟨4, by
    rintro _ ⟨g, rfl⟩
    have := abs_le.mp (halfDiff_abs_le m hm g (hG g g.2) x)
    linarith⟩

end RadGauss.Discrepancy

open MeasureTheory Pointwise RadGauss.Discrepancy in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i))
    (f₀ : X → ℝ) (hf₀ : f₀ ∈ F) :
    expectedMaxDiscrepancy μ m (F ∪ -F)
      ≤ 2 * expectedMaxDiscrepancy μ m F
        + expectedMaxDiscrepancy μ m ({f₀, -f₀} : Set (X → ℝ)) := by
  classical
  set P := Measure.pi (fun _ : Fin (2 * m) => μ) with hP
  set c : ℝ := 2 / ((2 * m : ℕ) : ℝ) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have : Nonempty F := hFne.to_subtype
  -- ranges
  have hneg : ∀ g ∈ -F, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro g hg x
    have h := hFrange (-g) (Set.mem_neg.mp hg) x
    simp only [Pi.neg_apply, Set.mem_Icc] at h ⊢
    constructor <;> linarith [h.1, h.2]
  have hU : ∀ g ∈ F ∪ -F, ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1 := by
    rintro g (hg | hg)
    · exact hFrange g hg
    · exact hneg g hg
  have hf₀neg : -f₀ ∈ -F := by rw [Set.mem_neg, neg_neg]; exact hf₀
  have hT : ∀ g ∈ ({f₀, -f₀} : Set (X → ℝ)), ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1 := by
    rintro g (rfl | rfl)
    · exact hFrange _ hf₀
    · exact hneg _ hf₀neg
  -- the three pointwise functions
  set A : (Fin (2 * m) → X) → ℝ := fun x => ⨆ f : F, halfDiff m (f : X → ℝ) x with hA
  set B : (Fin (2 * m) → X) → ℝ := fun x => ⨆ f : F, - halfDiff m (f : X → ℝ) x with hB
  set d : (Fin (2 * m) → X) → ℝ := fun x => halfDiff m f₀ x with hd
  have hdA : ∀ x, d x ≤ A x := fun x =>
    le_ciSup (f := fun f : F => halfDiff m (f : X → ℝ) x) (bdd m hm F hFrange x) ⟨f₀, hf₀⟩
  have hdB : ∀ x, - d x ≤ B x := fun x =>
    le_ciSup (f := fun f : F => - halfDiff m (f : X → ℝ) x) (bddNeg m hm F hFrange x) ⟨f₀, hf₀⟩
  have hd4 : ∀ x, |d x| ≤ 4 := fun x => halfDiff_abs_le m hm f₀ (hFrange _ hf₀) x
  have hA4 : ∀ x, A x ≤ 4 := fun x => ciSup_le fun f =>
    (abs_le.mp (halfDiff_abs_le m hm f (hFrange f f.2) x)).2
  have hB4 : ∀ x, B x ≤ 4 := fun x => ciSup_le fun f => by
    have := abs_le.mp (halfDiff_abs_le m hm f (hFrange f f.2) x); linarith
  -- measurability
  have hAm : Measurable A := by
    have : A = fun x => c * ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (decide (i.val < m)) *
        (f : X → ℝ) (x i) := by
      funext x
      rw [Real.mul_iSup_of_nonneg hc0]
      simp only [hA, halfDiff_eq, hcdef]
    rw [this]; exact (hsup _).const_mul c
  have hBm : Measurable B := by
    have : B = fun x => c * ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (decide ¬ (i.val < m)) *
        (f : X → ℝ) (x i) := by
      funext x
      rw [Real.mul_iSup_of_nonneg hc0]
      simp only [hB, neg_halfDiff_eq, hcdef]
    rw [this]; exact (hsup _).const_mul c
  have hdm : Measurable d := by
    have hf₀m := hFmeas f₀ hf₀
    have : d = fun x => c * ∑ i : Fin (2 * m), RadGauss.RiskBound.signVal (decide (i.val < m)) *
        f₀ (x i) := by
      funext x; simp only [hd, halfDiff_eq, hcdef]
    rw [this]
    refine Measurable.const_mul ?_ c
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (hf₀m.comp (measurable_pi_apply i)).const_mul _
  -- integrability
  have hAi : Integrable A P := by
    refine Integrable.of_bound hAm.aestronglyMeasurable 4 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have := hdA x; have := hd4 x; have := hA4 x
    exact abs_le.mpr ⟨by linarith [(abs_le.mp (hd4 x)).1], hA4 x⟩
  have hBi : Integrable B P := by
    refine Integrable.of_bound hBm.aestronglyMeasurable 4 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have := hdB x
    exact abs_le.mpr ⟨by linarith [(abs_le.mp (hd4 x)).2], hB4 x⟩
  have hdi : Integrable (fun x => |d x|) P := by
    refine Integrable.of_bound (hdm.abs).aestronglyMeasurable 4
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs]; exact hd4 x
  -- pointwise bounds
  have hE0 : ∀ x, 0 ≤ empiricalMaxDiscrepancy m (F ∪ -F) x := by
    intro x
    have h1 : d x ≤ empiricalMaxDiscrepancy m (F ∪ -F) x :=
      le_ciSup (f := fun g : ↥(F ∪ -F) => halfDiff m (g : X → ℝ) x) (bdd m hm _ hU x)
        ⟨f₀, Or.inl hf₀⟩
    have h2 : halfDiff m (-f₀) x ≤ empiricalMaxDiscrepancy m (F ∪ -F) x :=
      le_ciSup (f := fun g : ↥(F ∪ -F) => halfDiff m (g : X → ℝ) x) (bdd m hm _ hU x)
        ⟨-f₀, Or.inr hf₀neg⟩
    rw [halfDiff_neg] at h2
    have : d x = halfDiff m f₀ x := rfl
    linarith
  have hEle : ∀ x, empiricalMaxDiscrepancy m (F ∪ -F) x ≤ A x + B x + |d x| := by
    intro x
    have : Nonempty ↥(F ∪ -F) := ⟨⟨f₀, Or.inl hf₀⟩⟩
    refine ciSup_le fun g => ?_
    obtain ⟨g, hg⟩ := g
    rcases hg with hg | hg
    · have h1 : halfDiff m g x ≤ A x :=
        le_ciSup (f := fun f : F => halfDiff m (f : X → ℝ) x) (bdd m hm F hFrange x) ⟨g, hg⟩
      have := hdB x; have := le_abs_self (d x)
      show halfDiff m g x ≤ _
      linarith
    · have hg' : -g ∈ F := Set.mem_neg.mp hg
      have h1 : - halfDiff m (-g) x ≤ B x :=
        le_ciSup (f := fun f : F => - halfDiff m (f : X → ℝ) x) (bddNeg m hm F hFrange x) ⟨-g, hg'⟩
      rw [halfDiff_neg, neg_neg] at h1
      have := hdA x; have := neg_abs_le (d x)
      show halfDiff m g x ≤ _
      linarith
  have hC : ∀ x, empiricalMaxDiscrepancy m ({f₀, -f₀} : Set (X → ℝ)) x = |d x| := by
    intro x
    have : Nonempty ↥({f₀, -f₀} : Set (X → ℝ)) := ⟨⟨f₀, Set.mem_insert _ _⟩⟩
    apply le_antisymm
    · refine ciSup_le fun g => ?_
      obtain ⟨g, hg⟩ := g
      rcases hg with rfl | hg
      · exact le_abs_self _
      · rw [Set.mem_singleton_iff] at hg; subst hg
        show halfDiff m (-f₀) x ≤ _
        rw [halfDiff_neg]; exact neg_le_abs _
    · have h1 : halfDiff m f₀ x ≤ empiricalMaxDiscrepancy m ({f₀, -f₀} : Set (X → ℝ)) x :=
        le_ciSup (f := fun g : ↥({f₀, -f₀} : Set (X → ℝ)) => halfDiff m (g : X → ℝ) x)
          (bdd m hm _ hT x) ⟨f₀, Set.mem_insert _ _⟩
      have h2 : halfDiff m (-f₀) x ≤ empiricalMaxDiscrepancy m ({f₀, -f₀} : Set (X → ℝ)) x :=
        le_ciSup (f := fun g : ↥({f₀, -f₀} : Set (X → ℝ)) => halfDiff m (g : X → ℝ) x)
          (bdd m hm _ hT x) ⟨-f₀, Set.mem_insert_of_mem _ rfl⟩
      rw [halfDiff_neg] at h2
      exact abs_le'.mpr ⟨h1, h2⟩
  -- the swap
  have hBA : ∀ x, B x = A (fun i => x (swapFun m i)) := by
    intro x
    simp only [hA, hB, halfDiff_swap]
  have hmp : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (tau m) (MeasurableEquiv.refl X)) P P :=
    measurePreserving_arrowCongr' (fun _ => μ) (fun _ => μ) (tau m) (MeasurableEquiv.refl X)
      (fun _ => MeasurePreserving.id μ)
  have hintB : ∫ x, B x ∂P = ∫ x, A x ∂P := by
    rw [← hmp.integral_comp' A]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hBA x]
    rfl
  -- assemble
  have hDF : expectedMaxDiscrepancy μ m F = ∫ x, A x ∂P := rfl
  have hDT : expectedMaxDiscrepancy μ m ({f₀, -f₀} : Set (X → ℝ)) = ∫ x, |d x| ∂P := by
    unfold expectedMaxDiscrepancy
    exact integral_congr_ae (Filter.Eventually.of_forall hC)
  have hmono : expectedMaxDiscrepancy μ m (F ∪ -F) ≤ ∫ x, (A x + B x + |d x|) ∂P :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hE0) ((hAi.add hBi).add hdi)
      (Filter.Eventually.of_forall hEle)
  have e1 : ∫ x, (A x + B x + |d x|) ∂P = ∫ x, (A x + B x) ∂P + ∫ x, |d x| ∂P :=
    integral_add (hAi.add hBi) hdi
  have e2 : ∫ x, (A x + B x) ∂P = ∫ x, A x ∂P + ∫ x, B x ∂P := integral_add hAi hBi
  rw [hDF, hDT]
  linarith
