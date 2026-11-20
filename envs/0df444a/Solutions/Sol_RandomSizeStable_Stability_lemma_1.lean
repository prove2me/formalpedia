-- Prove2me | solution 1 for RandomSizeStable.Stability.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:23.450062+00:00
-- url     : https://prove2.me/submissions/11dbc97c-bf3b-4558-b56d-92c8f8998f50

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability

namespace RandomSizeStable.Dev.Common

/-- the factor attached to a draw `b` at label level `s`. -/
noncomputable def fac {V C : Type} (E : Election V C) (v : V) (c : C) (s : ℝ) (b : C) : ℝ := by
  classical
  exact if E.prefers v b c then 0 else if b = c then s else 1

theorem tupleWin_eq {V C : Type} (E : Election V C) (v : V) (c : C) {k : ℕ}
    (draws : Fin k → C) :
    tupleWin E v c draws = ∫ s in (0 : ℝ)..1, ∏ i, fac E v c s (draws i) := by
  classical
  unfold tupleWin
  by_cases h : ∃ i, E.prefers v (draws i) c
  · have h0 := h
    obtain ⟨i, hi⟩ := h0
    have : ∀ s : ℝ, ∏ i, fac E v c s (draws i) = 0 := fun s =>
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [fac, hi])
    simp only [this, h]
    simp
  · have h' : ∀ i, ¬ E.prefers v (draws i) c := fun i hi => h ⟨i, hi⟩
    have : ∀ s : ℝ, ∏ i, fac E v c s (draws i) =
        s ^ (Finset.univ.filter (fun i => draws i = c)).card := fun s => by
      simp only [fac, h', if_false]
      rw [Finset.prod_ite]
      simp
    simp only [this, h, if_false, integral_pow]
    simp

theorem fac_cont {V C : Type} (E : Election V C) (v : V) (c : C) (b : C) :
    Continuous (fun s : ℝ => fac E v c s b) := by
  unfold fac
  split_ifs <;> fun_prop

theorem sum_draws_eq {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (k : ℕ) :
    ∑ draws : Fin k → C, (∏ i, P (draws i)) * tupleWin E v c draws =
      ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ k := by
  classical
  have := E.isStrictTotalOrder v
  have h1 : ∀ s : ℝ, ∑ b, P b * fac E v c s b = leftRank E P v c + s * P c := by
    intro s
    unfold leftRank
    have : ∀ b, P b * fac E v c s b =
        (if E.prefers v c b then P b else 0) + (if b = c then s * P c else 0) := by
      intro b
      unfold fac
      rcases trichotomous_of (E.prefers v) b c with h | h | h
      · have h2 : ¬ E.prefers v c b := asymm h
        have h3 : b ≠ c := fun e => (irrefl_of (E.prefers v) c) (e ▸ h)
        simp [h, h2, h3]
      · subst h
        simp [irrefl_of (E.prefers v) b, mul_comm]
      · have h2 : ¬ E.prefers v b c := asymm h
        have h3 : b ≠ c := fun e => (irrefl_of (E.prefers v) c) (e ▸ h)
        simp [h, h2, h3]
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_filter]
    simp
  have h2 : ∀ draws : Fin k → C, (∏ i, P (draws i)) * tupleWin E v c draws =
      ∫ s in (0 : ℝ)..1, ∏ i, (P (draws i) * fac E v c s (draws i)) := by
    intro draws
    rw [tupleWin_eq, ← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    rw [Finset.prod_mul_distrib]
  simp only [h2]
  rw [← intervalIntegral.integral_finsetSum]
  · congr 1
    ext s
    rw [← h1 s, Finset.sum_pow']
    simp
  · intro draws _
    apply Continuous.intervalIntegrable
    have := fac_cont E v c
    fun_prop

theorem D_summable (D : PMF ℕ+) : Summable (fun k : ℕ+ => (D k).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

theorem pgf_hasSum (D : PMF ℕ+) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    HasSum (fun k : ℕ+ => (D k).toReal * t ^ (k : ℕ)) (pgf D t) := by
  have : Summable (fun k : ℕ+ => (D k).toReal * t ^ (k : ℕ)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (D_summable D)
    · exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg h0 _)
    · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ h0 h1)
  exact this.hasSum

theorem exch (D : PMF ℕ+) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (hrz : r + z ≤ 1) :
    HasSum (fun k : ℕ+ => (D k).toReal * ∫ s in (0 : ℝ)..1, (r + s * z) ^ (k : ℕ))
      (∫ s in (0 : ℝ)..1, pgf D (r + s * z)) := by
  have hx : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ r + s * z ∧ r + s * z ≤ 1 := by
    intro s hs
    refine ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (k : ℕ+) (s : ℝ) => (D k).toReal * (r + s * z) ^ (k : ℕ))
    (f := fun s => pgf D (r + s * z))
    (fun k _ => (D k).toReal)
    (fun k => by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (fun k => Filter.Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
      obtain ⟨h0, h1⟩ := hx t ht'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg h0 _))]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ h0 h1)))
    (Filter.Eventually.of_forall (fun t _ => D_summable D))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
      obtain ⟨h0, h1⟩ := hx t ht'
      exact pgf_hasSum D h0 h1))
  simpa [intervalIntegral.integral_const_mul] using this

theorem leftRank_bounds {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    0 ≤ leftRank E P v c ∧ 0 ≤ P c ∧ leftRank E P v c + P c ≤ 1 := by
  classical
  have := E.isStrictTotalOrder v
  refine ⟨Finset.sum_nonneg (fun b _ => hP.1 b), hP.1 c, ?_⟩
  unfold leftRank
  have hc : c ∉ Finset.univ.filter (fun b => E.prefers v c b) := by
    simp [irrefl_of (E.prefers v) c]
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := P) (Finset.subset_univ (insert c (Finset.univ.filter (fun b => E.prefers v c b))))
    (fun b _ _ => hP.1 b)
  rw [Finset.sum_insert hc, hP.2] at h
  linarith

theorem comparison_eq {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    comparison D E P v c = ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c) := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  refine ((exch D _ _ h0 h1 h2).tsum_eq.symm.trans ?_).symm
  unfold comparison
  congr 1
  ext k
  rw [sum_draws_eq]

end RandomSizeStable.Dev.Common
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common

namespace RandomSizeStable.Dev.L1

theorem leftRank_affine {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P Q : C → ℝ) (a b : ℝ) :
    leftRank E (a • P + b • Q) v c = a * leftRank E P v c + b * leftRank E Q v c := by
  unfold leftRank
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem A_bounds {V C : Type} [Fintype C] (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (k : ℕ) :
    0 ≤ ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ k ∧
    ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ k ≤ 1 := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  have hx : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ leftRank E P v c + s * P c ∧
      leftRank E P v c + s * P c ≤ 1 := by
    intro s hs
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  constructor
  · exact intervalIntegral.integral_nonneg zero_le_one
      (fun s hs => pow_nonneg (hx s hs).1 _)
  · have : ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ k ≤ ∫ s in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · apply Continuous.intervalIntegrable; fun_prop
      · exact intervalIntegrable_const
      · intro s hs
        exact pow_le_one₀ (hx s hs).1 (hx s hs).2
    simpa using this

theorem summ {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    Summable (fun k : ℕ+ => (D k).toReal *
      ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ (k : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (D_summable D)
  · exact mul_nonneg ENNReal.toReal_nonneg (A_bounds E v c P hP _).1
  · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (A_bounds E v c P hP _).2

theorem comparison_tsum {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) :
    comparison D E P v c = ∑' k : ℕ+, (D k).toReal *
      ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ (k : ℕ) := by
  unfold comparison
  congr 1
  ext k
  rw [sum_draws_eq]

theorem cont {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C) :
    ContinuousOn (fun P => comparison D E P v c) (stdSimplex ℝ C) := by
  classical
  unfold comparison
  apply continuousOn_tsum (u := fun k : ℕ+ => (D k).toReal)
  · intro k
    apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro draws _
    apply Continuous.mul _ continuous_const
    apply continuous_finsetProd
    intro i _
    exact continuous_apply _
  · exact D_summable D
  · intro k P hP
    rw [sum_draws_eq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (A_bounds E v c P hP _).1)]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (A_bounds E v c P hP _).2

theorem convex {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C) :
    ConvexOn ℝ (stdSimplex ℝ C) (fun P => comparison D E P v c) := by
  refine ⟨convex_stdSimplex ℝ C, ?_⟩
  intro P hP Q hQ a b ha hb hab
  have hR : a • P + b • Q ∈ stdSimplex ℝ C := convex_stdSimplex ℝ C hP hQ ha hb hab
  simp only [smul_eq_mul]
  rw [comparison_tsum, comparison_tsum, comparison_tsum]
  have hs1 := summ D E v c P hP
  have hs2 := summ D E v c Q hQ
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hs1.mul_left a) (hs2.mul_left b)]
  refine Summable.tsum_le_tsum (fun k => ?_) (summ D E v c _ hR)
    ((hs1.mul_left a).add (hs2.mul_left b))
  have hmono : ∫ s in (0 : ℝ)..1, (leftRank E (a • P + b • Q) v c +
        s * (a • P + b • Q) c) ^ (k : ℕ) ≤
      ∫ s in (0 : ℝ)..1, (a * (leftRank E P v c + s * P c) ^ (k : ℕ) +
        b * (leftRank E Q v c + s * Q c) ^ (k : ℕ)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    · intro s hs
      obtain ⟨p0, p1, p2⟩ := leftRank_bounds E v c P hP
      obtain ⟨q0, q1, q2⟩ := leftRank_bounds E v c Q hQ
      have hxP : 0 ≤ leftRank E P v c + s * P c := by nlinarith [hs.1]
      have hxQ : 0 ≤ leftRank E Q v c + s * Q c := by nlinarith [hs.1]
      have := (convexOn_pow (k : ℕ)).2 (Set.mem_Ici.2 hxP) (Set.mem_Ici.2 hxQ) ha hb hab
      simp only [smul_eq_mul] at this
      have e : leftRank E (a • P + b • Q) v c + s * (a • P + b • Q) c =
          a * (leftRank E P v c + s * P c) + b * (leftRank E Q v c + s * Q c) := by
        rw [leftRank_affine]; simp; ring
      rw [e]; exact this
  have hI : ∫ s in (0 : ℝ)..1, (a * (leftRank E P v c + s * P c) ^ (k : ℕ) +
        b * (leftRank E Q v c + s * Q c) ^ (k : ℕ)) =
      a * (∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ (k : ℕ)) +
        b * (∫ s in (0 : ℝ)..1, (leftRank E Q v c + s * Q c) ^ (k : ℕ)) := by
    have h1 : IntervalIntegrable (fun s : ℝ => a * (leftRank E P v c + s * P c) ^ (k : ℕ))
        volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have h2 : IntervalIntegrable (fun s : ℝ => b * (leftRank E Q v c + s * Q c) ^ (k : ℕ))
        volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have e1 : ∫ s in (0 : ℝ)..1, a * (leftRank E P v c + s * P c) ^ (k : ℕ) =
        a * ∫ s in (0 : ℝ)..1, (leftRank E P v c + s * P c) ^ (k : ℕ) :=
      intervalIntegral.integral_const_mul _ _
    have e2 : ∫ s in (0 : ℝ)..1, b * (leftRank E Q v c + s * Q c) ^ (k : ℕ) =
        b * ∫ s in (0 : ℝ)..1, (leftRank E Q v c + s * Q c) ^ (k : ℕ) :=
      intervalIntegral.integral_const_mul _ _
    have e3 := intervalIntegral.integral_add h1 h2
    rw [e1, e2] at e3
    exact e3
  rw [hI] at hmono
  have := mul_le_mul_of_nonneg_left hmono (ENNReal.toReal_nonneg (a := D k))
  nlinarith [this]

end RandomSizeStable.Dev.L1

namespace RandomSizeStable

open RandomSizeStable.Stability in
theorem chk_lemma_1 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (v : V) (c : C) :
    (∀ P ∈ stdSimplex ℝ C,
      comparison D E P v c =
        ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c)) ∧
    (∀ P ∈ stdSimplex ℝ C, 0 < P c →
      comparison D E P v c = (P c)⁻¹ *
        ∫ u in (leftRank E P v c)..(leftRank E P v c + P c), pgf D u) ∧
    ContinuousOn (fun P => comparison D E P v c) (stdSimplex ℝ C) ∧
    ConvexOn ℝ (stdSimplex ℝ C) (fun P => comparison D E P v c) := by
  refine ⟨fun P hP => RandomSizeStable.Dev.Common.comparison_eq D E v c P hP, ?_,
    RandomSizeStable.Dev.L1.cont D E v c, RandomSizeStable.Dev.L1.convex D E v c⟩
  intro P hP hz
  rw [RandomSizeStable.Dev.Common.comparison_eq D E v c P hP]
  have := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (f := pgf D) (c := P c) hz.ne' (leftRank E P v c)
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at this
  have e : ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c) =
      ∫ x in (0 : ℝ)..1, pgf D (P c * x + leftRank E P v c) := by
    congr 1; ext s; ring_nf
  rw [e, this]
  congr 2
  ring

end RandomSizeStable

end

theorem solution : type_of% @RandomSizeStable.chk_lemma_1 := @RandomSizeStable.chk_lemma_1
