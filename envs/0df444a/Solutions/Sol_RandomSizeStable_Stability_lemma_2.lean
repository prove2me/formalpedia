-- Prove2me | solution 1 for RandomSizeStable.Stability.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:23.642957+00:00
-- url     : https://prove2.me/submissions/8df5e4c8-d160-4977-9b78-ddaec09ac0c1

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability
import Theorems.Thm_RandomSizeStable_Stability_theorem_3

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

theorem comparison_eq2 {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    P c * comparison D E P v c =
      ∫ u in (leftRank E P v c)..(leftRank E P v c + P c), pgf D u := by
  rcases (leftRank_bounds E v c P hP).2.1.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [comparison_eq D E v c P hP]
    have := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
      (f := pgf D) (c := P c) h.ne' (leftRank E P v c)
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at this
    have e : ∫ s in (0 : ℝ)..1, pgf D (leftRank E P v c + s * P c) =
        ∫ x in (0 : ℝ)..1, pgf D (P c * x + leftRank E P v c) := by
      congr 1; ext s; ring_nf
    rw [e, this, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul, add_comm]

theorem pgf_contOn (D : PMF ℕ+) : ContinuousOn (pgf D) (Set.Icc (0 : ℝ) 1) := by
  unfold pgf
  refine continuousOn_tsum (u := fun k : ℕ+ => (D k).toReal) (fun k => ?_) (D_summable D)
    (fun k t ht => ?_)
  · exact (continuous_const.mul (continuous_pow _)).continuousOn
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg ht.1 _))]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ ht.1 ht.2)

theorem pgf_integrable (D : PMF ℕ+) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : IntervalIntegrable (pgf D) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact (pgf_contOn D).mono (Set.uIcc_subset_Icc ha hb)

end RandomSizeStable.Dev.Common
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common

namespace RandomSizeStable.Dev.L2

theorem leftRank_sep {V C : Type} [Fintype C] (E : Election V C) (v : V) (c j : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (h : E.prefers v c j) :
    leftRank E P v j + P j ≤ leftRank E P v c := by
  classical
  have := E.isStrictTotalOrder v
  have hj : j ∉ Finset.univ.filter (fun b => E.prefers v j b) := by
    simp [irrefl_of (E.prefers v) j]
  have hsub : insert j (Finset.univ.filter (fun b => E.prefers v j b)) ⊆
      Finset.univ.filter (fun b => E.prefers v c b) := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hb
    · exact h
    · exact trans_of (E.prefers v) h hb
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := P) hsub (fun b _ _ => hP.1 b)
  rw [Finset.sum_insert hj] at this
  unfold leftRank
  linarith

theorem block_disjoint {V C : Type} [Fintype C] (E : Election V C) (v : V) (c j : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (hne : c ≠ j) :
    Disjoint (rankBlock E P v c) (rankBlock E P v j) := by
  have := E.isStrictTotalOrder v
  rcases trichotomous_of (E.prefers v) c j with h | h | h
  · have := leftRank_sep E v c j P hP h
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [rankBlock, Set.mem_Ico] at hx hx'
    linarith [hx.1, hx'.2]
  · exact absurd h hne
  · have := leftRank_sep E v j c P hP h
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [rankBlock, Set.mem_Ico] at hx hx'
    linarith [hx.2, hx'.1]

theorem block_integral {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    ∫ u in rankBlock E P v c, (pgf D u - benchmark D) =
      P c * comparison D E P v c - P c * benchmark D := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  have ha : leftRank E P v c ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, by linarith⟩
  have hb : leftRank E P v c + P c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  unfold rankBlock
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_sub (pgf_integrable D ha hb) intervalIntegrable_const,
    ← comparison_eq2 D E v c P hP]
  simp

theorem integrableOn_block {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V)
    (c : C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    IntegrableOn (fun u => pgf D u - benchmark D) (rankBlock E P v c) volume := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
  have hc : ContinuousOn (fun u => pgf D u - benchmark D) (Set.Icc (0:ℝ) 1) :=
    (pgf_contOn D).sub continuousOn_const
  refine (hc.integrableOn_Icc).mono_set ?_
  intro x hx
  simp only [rankBlock, Set.mem_Ico] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

open Classical in
theorem region_integral {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (H : Set C) :
    ∫ u in markedRegion E P v H, (pgf D u - benchmark D) =
      ∑ c ∈ (Finset.univ.filter (fun c => c ∈ H)),
        (P c * comparison D E P v c - P c * benchmark D) := by
  classical
  have hset : markedRegion E P v H =
      ⋃ c ∈ (Finset.univ.filter (fun c => c ∈ H)), rankBlock E P v c := by
    ext x
    simp [markedRegion]
  rw [hset, integral_biUnion_finset]
  · exact Finset.sum_congr rfl (fun c _ => block_integral D E v c P hP)
  · intro c _
    exact measurableSet_Ico
  · intro c _ j _ hne
    exact block_disjoint E v c j P hP hne
  · intro c _
    exact integrableOn_block D E v c P hP

theorem pgf_mono (D : PMF ℕ+) {x y : ℝ} (h0 : 0 ≤ x) (hxy : x ≤ y) (h1 : y ≤ 1) :
    pgf D x ≤ pgf D y := by
  refine hasSum_le (fun k => ?_) (pgf_hasSum D h0 (hxy.trans h1)) (pgf_hasSum D (h0.trans hxy) h1)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hxy _) ENNReal.toReal_nonneg

theorem pgf_le_comparison {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V)
    (o : C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    pgf D (leftRank E P v o) ≤ comparison D E P v o := by
  obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v o P hP
  rw [comparison_eq D E v o P hP]
  have hint : IntervalIntegrable (fun s : ℝ => pgf D (leftRank E P v o + s * P o)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine (pgf_contOn D).comp (by fun_prop) ?_
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have := intervalIntegral.integral_mono_on (zero_le_one' ℝ)
    (intervalIntegrable_const (c := pgf D (leftRank E P v o))) hint (fun s hs =>
      pgf_mono D h0 (by nlinarith [hs.1]) (by nlinarith [hs.2]))
  simpa using this

end RandomSizeStable.Dev.L2

namespace RandomSizeStable

open RandomSizeStable.Stability in
theorem chk_lemma_2 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (hP : IsStable D E P) :
    (∀ H : Set C, voterMean (fun v =>
      ∫ u in markedRegion E P v H, (pgf D u - benchmark D)) = 0) ∧
    (∀ o : C, voterMean (fun v => pgf D (leftRank E P v o)) ≤ benchmark D) := by
  classical
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ)⁻¹ := by positivity
  have hsupp := (RandomSizeStable.Stability.theorem_3 D).2.2 V C E P hP
  have hscore : ∀ c, P c * score D E P c = P c * benchmark D := by
    intro c
    rcases (hP.1.1 c).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [hsupp c h]
  refine ⟨fun H => ?_, fun o => ?_⟩
  · simp only [Dev.L2.region_integral D E _ P hP.1 H]
    unfold voterMean
    rw [Finset.sum_comm]
    have : ∀ c, ∑ v, (P c * comparison D E P v c - P c * benchmark D) = 0 := by
      intro c
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have h := hscore c
      unfold score voterMean at h
      have hn' : (Fintype.card V : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos (α := V)).ne'
      field_simp at h ⊢
      simp only [Finset.card_univ]
      linarith
    simp [this]
  · calc voterMean (fun v => pgf D (leftRank E P v o))
        ≤ voterMean (fun v => comparison D E P v o) := by
          unfold voterMean
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun v _ => Dev.L2.pgf_le_comparison D E v o P hP.1)) hn
      _ = score D E P o := rfl
      _ ≤ benchmark D := hP.2 o

end RandomSizeStable

end

theorem solution : type_of% @RandomSizeStable.chk_lemma_2 := @RandomSizeStable.chk_lemma_2
