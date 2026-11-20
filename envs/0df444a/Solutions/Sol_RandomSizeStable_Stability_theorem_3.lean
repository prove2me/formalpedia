-- Prove2me | solution 1 for RandomSizeStable.Stability.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:23.702145+00:00
-- url     : https://prove2.me/submissions/6462ac0b-6dfc-412c-a86b-4bfac51dc6b4

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability
import Theorems.Thm_RandomSizeStable_Stability_lemma_1

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

/-- telescoping of the rank blocks of a voter. -/
theorem tiling {V C : Type} [Fintype C] (E : Election V C) (v : V)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) (F : ℝ → ℝ) :
    ∑ c, (F (leftRank E P v c + P c) - F (leftRank E P v c)) = F 1 - F 0 := by
  classical
  have hsto := E.isStrictTotalOrder v
  let _ : LinearOrder C := linearOrderOfSTO (E.prefers v)
  have key : ∀ s : Finset C, (∀ c ∈ s, ∀ b, E.prefers v c b → b ∈ s) →
      ∑ c ∈ s, (F (leftRank E P v c + P c) - F (leftRank E P v c)) =
        F (∑ c ∈ s, P c) - F 0 := by
    intro s
    induction s using Finset.induction_on_min with
    | empty => intro _; simp
    | insert a s hlt ih =>
      intro hcl
      have has : a ∉ s := fun h => irrefl_of (E.prefers v) a (hlt a h)
      have hcl' : ∀ c ∈ s, ∀ b, E.prefers v c b → b ∈ s := by
        intro c hc b hb
        have h1 := hcl c (Finset.mem_insert_of_mem hc) b hb
        rcases Finset.mem_insert.1 h1 with h | h
        · rw [h] at hb; exact absurd (hlt c hc) (asymm_of (E.prefers v) hb)
        · exact h
      have hr : leftRank E P v a = ∑ b ∈ s, P b := by
        unfold leftRank
        congr 1
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hb
          rcases Finset.mem_insert.1 (hcl a (Finset.mem_insert_self a s) b hb) with h | h
          · subst h; exact absurd hb (irrefl_of (E.prefers v) b)
          · exact h
        · intro hb; exact hlt b hb
      rw [Finset.sum_insert has, Finset.sum_insert has, ih hcl', hr]
      ring_nf
  have := key Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  rw [this, hP.2]

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

theorem integral_pgf_eq_benchmark (D : PMF ℕ+) :
    ∫ s in (0 : ℝ)..1, pgf D s = benchmark D := by
  have h := exch D 0 1 le_rfl zero_le_one (by norm_num)
  simp only [zero_add, mul_one] at h
  rw [← h.tsum_eq]
  unfold benchmark
  congr 1
  ext k
  rw [integral_pow]
  simp [div_eq_mul_inv]

/-- Self-play identity: against a lottery `P` in the simplex, the `P`-weighted average of the
comparison scores of all candidates (for a fixed voter) is exactly the benchmark. -/
theorem selfplay {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V)
    (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    ∑ c, P c * comparison D E P v c = benchmark D := by
  have h1 : ∀ c, P c * comparison D E P v c =
      (∫ u in (0:ℝ)..(leftRank E P v c + P c), pgf D u) -
        ∫ u in (0:ℝ)..(leftRank E P v c), pgf D u := by
    intro c
    obtain ⟨h0, h1, h2⟩ := leftRank_bounds E v c P hP
    rw [comparison_eq2 D E v c P hP]
    have ha : leftRank E P v c ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, by linarith⟩
    have hb : leftRank E P v c + P c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    rw [← intervalIntegral.integral_interval_sub_left (pgf_integrable D h0m hb)
      (pgf_integrable D h0m ha)]
  simp only [h1]
  rw [tiling E v P hP (fun x => ∫ u in (0:ℝ)..x, pgf D u)]
  simp [integral_pgf_eq_benchmark]

end RandomSizeStable.Dev.Common
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common

namespace RandomSizeStable.Dev.T3

theorem score_avg {V C : Type} [Fintype V] [Nonempty V] [Fintype C] (D : PMF ℕ+)
    (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C) :
    ∑ c, P c * score D E P c = benchmark D := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := V)).ne'
  have h1 : ∀ c, P c * score D E P c =
      (Fintype.card V : ℝ)⁻¹ * ∑ v, P c * comparison D E P v c := by
    intro c
    unfold score voterMean
    rw [← Finset.mul_sum]
    ring
  simp only [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [selfplay D E _ P hP]
  simp [hn]

theorem score_contOn {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (c : C) :
    ContinuousOn (fun P => score D E P c) (stdSimplex ℝ C) := by
  unfold score voterMean
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro v _
  exact (RandomSizeStable.Stability.lemma_1 D E v c).2.2.1

theorem score_convex {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (c : C) (P Q : C → ℝ) (hP : P ∈ stdSimplex ℝ C)
    (hQ : Q ∈ stdSimplex ℝ C) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    score D E (a • P + b • Q) c ≤ a * score D E P c + b * score D E Q c := by
  unfold score voterMean
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ)⁻¹ := by positivity
  have h : ∑ v, comparison D E (a • P + b • Q) v c ≤
      ∑ v, (a * comparison D E P v c + b * comparison D E Q v c) := by
    apply Finset.sum_le_sum
    intro v _
    have := (RandomSizeStable.Stability.lemma_1 D E v c).2.2.2.2 hP hQ ha hb hab
    simpa using this
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  nlinarith [mul_le_mul_of_nonneg_left h hn]

theorem exists_stable {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) : ∃ P : C → ℝ, IsStable D E P := by
  classical
  set K : Set (C → ℝ) := stdSimplex ℝ C with hK
  let f : (C → ℝ) → (C → ℝ) → ℝ := fun x y => ∑ c, y c * (score D E x c - benchmark D)
  obtain ⟨c0⟩ := (inferInstance : Nonempty C)
  have hne : K.Nonempty := ⟨Pi.single c0 1, single_mem_stdSimplex ℝ c0⟩
  have hconv : Convex ℝ K := convex_stdSimplex ℝ C
  have hcomp : IsCompact K := isCompact_stdSimplex ℝ C
  have hcont : ∀ y ∈ K, ContinuousOn (fun x => f x y) K := by
    intro y _
    apply continuousOn_finsetSum
    intro c _
    exact continuousOn_const.mul ((score_contOn D E c).sub continuousOn_const)
  have hconvex : ∀ y ∈ K, ConvexOn ℝ K (fun x => f x y) := by
    intro y hy
    refine ⟨hconv, ?_⟩
    intro P hP Q hQ a b ha hb hab
    simp only [smul_eq_mul]
    have : ∀ c ∈ (Finset.univ : Finset C), y c * (score D E (a • P + b • Q) c - benchmark D) ≤
        a * (y c * (score D E P c - benchmark D)) + b * (y c * (score D E Q c - benchmark D)) := by
      intro c _
      have h := score_convex D E c P Q hP hQ a b ha hb hab
      have hy := hy.1 c
      have : b = 1 - a := by linarith
      subst this
      nlinarith [mul_le_mul_of_nonneg_left h hy]
    have h := Finset.sum_le_sum this
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
    exact h
  have hlin : ∀ x ∈ K, ConcaveOn ℝ K (fun y => f x y) := by
    intro x _
    have : (fun y => f x y) = ⇑(∑ c, (score D E x c - benchmark D) • (LinearMap.proj c :
        (C → ℝ) →ₗ[ℝ] ℝ)) := by
      ext y
      simp [f, LinearMap.sum_apply, mul_comm]
    rw [this]
    exact LinearMap.concaveOn _ hconv
  have hlinc : ∀ x ∈ K, ContinuousOn (fun y => f x y) K := by
    intro x _
    apply Continuous.continuousOn
    apply continuous_finsetSum
    intro c _
    exact (continuous_apply c).mul continuous_const
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn (X := K) (Y := K) (f := f)
    hne hconv hcomp (fun y hy => (hcont y hy).lowerSemicontinuousOn)
    (fun y hy => (hconvex y hy).quasiconvexOn) hconv hne hcomp
    (fun x hx => (hlinc x hx).upperSemicontinuousOn)
    (fun x hx => (hlin x hx).quasiconcaveOn)
  have hbb : f b b = 0 := by
    simp only [f, mul_sub, Finset.sum_sub_distrib, score_avg D E b hb, ← Finset.sum_mul, hb.2]
    ring
  refine ⟨a, ha, fun c => ?_⟩
  have := hsad b hb (Pi.single c 1) (single_mem_stdSimplex ℝ c)
  rw [hbb] at this
  simp only [f, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  linarith

end RandomSizeStable.Dev.T3

namespace RandomSizeStable

open RandomSizeStable.Stability in
theorem chk_theorem_3 (D : PMF ℕ+) :
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C), ∃ P : C → ℝ, IsStable D E P) ∧
    (∀ α : ℝ, α < benchmark D →
      ∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m) (E : Election (Fin n) (Fin m)),
        ∀ P ∈ stdSimplex ℝ (Fin m), ∃ c, α < score D E P c) ∧
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C) (P : C → ℝ), IsStable D E P →
        ∀ c, 0 < P c → score D E P c = benchmark D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V C _ _ _ _ E
    exact RandomSizeStable.Dev.T3.exists_stable D E
  · intro α hα
    refine ⟨1, 1, one_pos, one_pos, ⟨fun _ a b => a < b, fun _ => inferInstance⟩, ?_⟩
    intro P hP
    by_contra hcon
    push Not at hcon
    have h1 := RandomSizeStable.Dev.T3.score_avg D
      (⟨fun _ a b => a < b, fun _ => inferInstance⟩ : Election (Fin 1) (Fin 1)) P hP
    have h2 : ∑ c, P c * score D (⟨fun _ a b => a < b, fun _ => inferInstance⟩ :
        Election (Fin 1) (Fin 1)) P c ≤ ∑ c, P c * α :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hcon c) (hP.1 c))
    rw [← Finset.sum_mul, hP.2, one_mul] at h2
    linarith
  · intro V C _ _ _ _ E P hP c hc
    have h1 := RandomSizeStable.Dev.T3.score_avg D E P hP.1
    have h2 : ∀ c', P c' * (score D E P c' - benchmark D) ≤ 0 := fun c' =>
      mul_nonpos_of_nonneg_of_nonpos (hP.1.1 c') (sub_nonpos.2 (hP.2 c'))
    have h3 : ∑ c', P c' * (score D E P c' - benchmark D) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, hP.1.2]
      ring
    have h4 := (Finset.sum_eq_zero_iff_of_nonpos (fun c' _ => h2 c')).1 h3 c (Finset.mem_univ _)
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hc.ne'
    · linarith

end RandomSizeStable

end

theorem solution : type_of% @RandomSizeStable.chk_theorem_3 := @RandomSizeStable.chk_theorem_3
