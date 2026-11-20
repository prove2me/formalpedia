-- Prove2me | solution 1 for RandomSizeStable.Stability.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:58:00.405806+00:00
-- url     : https://prove2.me/submissions/583c5c26-152f-49ba-811d-ae3c57e3fa0f

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks
import Definitions.Def_RandomSizeStable_Stability_Stability
import Definitions.Def_RandomSizeStable_Stability_DrawLaw
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Theorems.Thm_RandomSizeStable_Stability_lemma_1
import Definitions.Def_RandomSizeStable_Stability_VotingRule

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

open MeasureTheory RandomSizeStable.Stability RandomSizeStable.Dev.Common

namespace RandomSizeStable.Dev.T2a

/-- the elementary inequality (paper §6), `c = 71/125, p = 3/4, a = 1/52, b = 7/26`. -/
theorem elem (k : ℕ) (hk : 1 ≤ k) :
    (7/26 : ℝ) ^ (k + 1) + (71/125 - 7/26) * ((k : ℝ) + 1) * (71/125) ^ k <
      (71/125 - 1/52) * (3/4) ^ k + (1/52) ^ (k + 1) := by
  have hpos : (0 : ℝ) < (1/52) ^ (k + 1) := by positivity
  have key : ∀ m : ℕ, 3 ≤ m →
      (7/26 : ℝ) ^ (m + 1) + (71/125 - 7/26) * ((m : ℝ) + 1) * (71/125) ^ m <
        (71/125 - 1/52) * (3/4) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have h1 : (7/26 : ℝ) ^ (m + 1 + 1) ≤ (3/4) * (7/26 : ℝ) ^ (m + 1) := by
        rw [pow_succ]
        nlinarith [pow_pos (show (0:ℝ) < 7/26 by norm_num) (m + 1)]
      have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have h2 : (71/125 - 7/26 : ℝ) * (((m + 1 : ℕ) : ℝ) + 1) * (71/125) ^ (m + 1) ≤
          (3/4) * ((71/125 - 7/26) * ((m : ℝ) + 1) * (71/125) ^ m) := by
        have hc : (0 : ℝ) < (71/125) ^ m := by positivity
        push_cast
        rw [pow_succ]
        have : (0:ℝ) ≤ (71/125 - 7/26) * (71/125) ^ m := by
          have : (0:ℝ) ≤ 71/125 - 7/26 := by norm_num
          positivity
        nlinarith [mul_nonneg this (show (0:ℝ) ≤ (3/4) * ((m:ℝ)+1) - (71/125) * ((m:ℝ) + 2) by
          nlinarith)]
      rw [pow_succ (3/4 : ℝ) m]
      nlinarith
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k <;> norm_num
  · linarith [key k h]

/-- `∫₀¹ (l + s w)^k ds`. -/
noncomputable def J (k : ℕ) (l w : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, (l + s * w) ^ k

theorem J_formula (k : ℕ) (l w : ℝ) (hw : w ≠ 0) :
    J k l w = ((l + w) ^ (k + 1) - l ^ (k + 1)) / ((k + 1) * w) := by
  unfold J
  have := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
      (f := fun x : ℝ => x ^ k) (c := w) hw l
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at this
  have e : ∫ s in (0 : ℝ)..1, (l + s * w) ^ k = ∫ x in (0 : ℝ)..1, (w * x + l) ^ k := by
    congr 1; ext s; ring_nf
  rw [e, this, integral_pow]
  rw [add_comm l w]
  field_simp

theorem J_bounds (k : ℕ) (l w : ℝ) (hl : 0 ≤ l) (hw : 0 ≤ w) (hlw : l + w ≤ 1) :
    0 ≤ J k l w ∧ J k l w ≤ 1 := by
  unfold J
  have hx : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ l + s * w ∧ l + s * w ≤ 1 := by
    intro s hs
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  constructor
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro s hs
    exact pow_nonneg (hx s hs).1 _
  · have : ∫ s in (0:ℝ)..1, (1:ℝ) = 1 := by simp
    have h := intervalIntegral.integral_mono_on (f := fun s : ℝ => (l + s * w) ^ k)
      (g := fun _ => (1:ℝ)) (μ := volume) (a := 0) (b := 1) zero_le_one
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const
      (fun s hs => pow_le_one₀ (hx s hs).1 (hx s hs).2)
    rw [this] at h
    exact h

/-- the series for the score of `o`. -/
noncomputable def Sc (D : PMF ℕ+) (l w : ℝ) : ℝ :=
  ∑' k : ℕ+, (D k).toReal * J (k : ℕ) l w

theorem Sc_summable (D : PMF ℕ+) (l w : ℝ) (hl : 0 ≤ l) (hw : 0 ≤ w) (hlw : l + w ≤ 1) :
    Summable (fun k : ℕ+ => (D k).toReal * J (k : ℕ) l w) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (D_summable D)
  · exact mul_nonneg ENNReal.toReal_nonneg (J_bounds _ l w hl hw hlw).1
  · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (J_bounds _ l w hl hw hlw).2

/-- case B of the paper. -/
theorem caseB (D : PMF ℕ+) (h : benchmark D ≤ pgf D (71/125)) :
    ((3/4 : ℝ) / (3/4 + 71/125 - 1/52)) * Sc D (1/52) (1/4) +
      (1 - (3/4 : ℝ) / (3/4 + 71/125 - 1/52)) * Sc D (3/4) (1/4) < benchmark D := by
  set z0 : ℝ := (3/4 : ℝ) / (3/4 + 71/125 - 1/52) with hz0
  have hz0' : z0 = 1625 / 2814 := by rw [hz0]; norm_num
  have s1 := Sc_summable D (1/52) (1/4) (by norm_num) (by norm_num) (by norm_num)
  have s2 := Sc_summable D (3/4) (1/4) (by norm_num) (by norm_num) (by norm_num)
  have hsb : Summable (fun k : ℕ+ => (D k).toReal / ((k : ℕ) + 1 : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (D_summable D)
    · positivity
    · have : (1 : ℝ) ≤ ((k : ℕ) + 1 : ℝ) := by
        have := k.pos; exact_mod_cast (by omega : 1 ≤ (k : ℕ) + 1)
      exact div_le_self ENNReal.toReal_nonneg this
  have hsc : Summable (fun k : ℕ+ => (D k).toReal * (71/125 : ℝ) ^ (k : ℕ)) :=
    (pgf_hasSum D (by norm_num) (by norm_num)).summable
  -- lambda
  set lam : ℝ := 4 * z0 * (71/125 - 7/26) with hlam
  have hlam0 : 0 < lam := by rw [hlam, hz0']; norm_num
  have hF : Summable (fun k : ℕ+ => (D k).toReal * (z0 * J (k:ℕ) (1/52) (1/4) +
      (1 - z0) * J (k:ℕ) (3/4) (1/4) - 1 / ((k : ℕ) + 1 : ℝ))) := by
    have := ((s1.mul_left z0).add (s2.mul_left (1 - z0))).sub hsb
    refine this.congr (fun k => ?_)
    ring
  have hH : Summable (fun k : ℕ+ => lam * ((D k).toReal / ((k : ℕ) + 1 : ℝ) -
      (D k).toReal * (71/125 : ℝ) ^ (k : ℕ))) := (hsb.sub hsc).mul_left lam
  -- pointwise
  have pt : ∀ k : ℕ+, z0 * J (k:ℕ) (1/52) (1/4) + (1 - z0) * J (k:ℕ) (3/4) (1/4) -
      1 / ((k : ℕ) + 1 : ℝ) < lam * (1 / ((k : ℕ) + 1 : ℝ) - (71/125 : ℝ) ^ (k : ℕ)) := by
    intro k
    have hk1 : 1 ≤ (k : ℕ) := k.pos
    have E := elem (k : ℕ) hk1
    rw [J_formula _ _ _ (by norm_num), J_formula _ _ _ (by norm_num)]
    have hx : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
    have e1 : (1/52 + 1/4 : ℝ) = 7/26 := by norm_num
    have e2 : (3/4 + 1/4 : ℝ) = 1 := by norm_num
    rw [e1, e2, one_pow]
    rw [← sub_neg]
    have : z0 * (((7/26 : ℝ) ^ ((k:ℕ) + 1) - (1/52) ^ ((k:ℕ) + 1)) / (((k:ℕ) + 1) * (1/4))) +
        (1 - z0) * ((1 - (3/4 : ℝ) ^ ((k:ℕ) + 1)) / (((k:ℕ) + 1) * (1/4))) -
        1 / (((k : ℕ) : ℝ) + 1) - lam * (1 / (((k : ℕ) : ℝ) + 1) - (71/125 : ℝ) ^ (k : ℕ)) =
        (4 * z0 * ((7/26 : ℝ) ^ ((k:ℕ) + 1) - (1/52) ^ ((k:ℕ) + 1)) +
          4 * (1 - z0) * (1 - (3/4 : ℝ) ^ ((k:ℕ) + 1)) - 1 - lam +
          lam * (((k:ℕ) : ℝ) + 1) * (71/125 : ℝ) ^ (k : ℕ)) / (((k : ℕ) : ℝ) + 1) := by
      field_simp
      ring
    rw [this]
    apply div_neg_of_neg_of_pos _ hx
    rw [hlam, hz0', pow_succ (3/4 : ℝ)]
    nlinarith [E]
  have hle : ∀ k : ℕ+, (D k).toReal * (z0 * J (k:ℕ) (1/52) (1/4) +
      (1 - z0) * J (k:ℕ) (3/4) (1/4) - 1 / ((k : ℕ) + 1 : ℝ)) ≤
      lam * ((D k).toReal / ((k : ℕ) + 1 : ℝ) - (D k).toReal * (71/125 : ℝ) ^ (k : ℕ)) := by
    intro k
    have := (pt k).le
    have h0 := ENNReal.toReal_nonneg (a := D k)
    calc _ ≤ (D k).toReal * (lam * (1 / ((k : ℕ) + 1 : ℝ) - (71/125 : ℝ) ^ (k : ℕ))) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  obtain ⟨k0, hk0⟩ : ∃ k : ℕ+, 0 < (D k).toReal := by
    by_contra hcon
    push Not at hcon
    have : ∀ k : ℕ+, (D k).toReal = 0 := fun k => le_antisymm (hcon k) ENNReal.toReal_nonneg
    have h1 : (∑' k : ℕ+, (D k).toReal) = 1 := by
      have := PMF.tsum_coe D
      have h2 := ENNReal.tsum_toReal_eq (f := fun k : ℕ+ => D k) (fun k => PMF.apply_ne_top D k)
      rw [this] at h2
      simpa using h2.symm
    simp [this] at h1
  have hlt : (D k0).toReal * (z0 * J (k0:ℕ) (1/52) (1/4) +
      (1 - z0) * J (k0:ℕ) (3/4) (1/4) - 1 / ((k0 : ℕ) + 1 : ℝ)) <
      lam * ((D k0).toReal / ((k0 : ℕ) + 1 : ℝ) - (D k0).toReal * (71/125 : ℝ) ^ (k0 : ℕ)) := by
    calc _ < (D k0).toReal * (lam * (1 / ((k0 : ℕ) + 1 : ℝ) - (71/125 : ℝ) ^ (k0 : ℕ))) :=
          mul_lt_mul_of_pos_left (pt k0) hk0
      _ = _ := by ring
  have hsum := Summable.tsum_lt_tsum hle hlt hF hH
  -- evaluate
  have e1 : ∑' k : ℕ+, (D k).toReal * (z0 * J (k:ℕ) (1/52) (1/4) +
      (1 - z0) * J (k:ℕ) (3/4) (1/4) - 1 / ((k : ℕ) + 1 : ℝ)) =
      z0 * Sc D (1/52) (1/4) + (1 - z0) * Sc D (3/4) (1/4) - benchmark D := by
    unfold Sc benchmark
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (s1.mul_left z0) (s2.mul_left (1 - z0)),
      ← Summable.tsum_sub ((s1.mul_left z0).add (s2.mul_left (1 - z0))) hsb]
    congr 1; ext k
    ring
  have e2 : ∑' k : ℕ+, lam * ((D k).toReal / ((k : ℕ) + 1 : ℝ) -
      (D k).toReal * (71/125 : ℝ) ^ (k : ℕ)) = lam * (benchmark D - pgf D (71/125)) := by
    rw [tsum_mul_left, Summable.tsum_sub hsb hsc]
    rfl
  rw [e1, e2] at hsum
  nlinarith

/-- a rational slightly below `z0`. -/
theorem exists_rat_z (A B μ z0 : ℝ) (hz : 0 < z0) (h : z0 * A + (1 - z0) * B < μ) :
    ∃ zn zd : ℕ, 0 < zn ∧ 0 < zd ∧ (zn : ℝ) / zd < z0 ∧
      ((zn : ℝ) / zd) * A + (1 - (zn : ℝ) / zd) * B < μ := by
  set δ := μ - (z0 * A + (1 - z0) * B) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ε := δ / (|A - B| + 1) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (z0 - ε) < z0 from
    max_lt hz (by linarith))
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq3 : z0 - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqpos : 0 < q := by exact_mod_cast hq0
  refine ⟨q.num.toNat, q.den, ?_, q.den_pos, ?_, ?_⟩
  · have := Rat.num_pos.2 hqpos
    omega
  · have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_pos.2 hqpos).le
      have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
      rw [h2]
      exact_mod_cast Rat.num_div_den q
    rw [this]; exact hq2
  · have : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_pos.2 hqpos).le
      have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
      rw [h2]
      exact_mod_cast Rat.num_div_den q
    rw [this]
    have hd : -δ < (z0 - (q:ℝ)) * (A - B) := by
      have h1 : -((z0 - q) * |A - B|) ≤ (z0 - (q:ℝ)) * (A - B) := by
        have := mul_le_mul_of_nonneg_left (neg_abs_le (A - B)) (show 0 ≤ z0 - (q:ℝ) by linarith)
        linarith
      have h2 : (z0 - (q:ℝ)) * |A - B| ≤ ε * |A - B| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      have h3 : ε * |A - B| < δ := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (A - B)]
      linarith
    nlinarith

theorem Sc_zero (D : PMF ℕ+) (l : ℝ) : Sc D l 0 = pgf D l := by
  unfold Sc J pgf
  congr 1; ext k
  simp

end RandomSizeStable.Dev.T2a

end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common

namespace RandomSizeStable.Dev.T2b

/-! ### Equivariance and transport -/

theorem leftRank_equiv {V V' C C' : Type} [Fintype C] [Fintype C'] (E : Election V C)
    (E' : Election V' C') (φ : C ≃ C') (ψ : V ≃ V')
    (hψ : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b)
    (P' : C' → ℝ) (v : V) (c : C) :
    leftRank E' P' (ψ v) (φ c) = leftRank E (P' ∘ φ) v c := by
  classical
  unfold leftRank
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp φ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Function.comp, hψ]

theorem simplex_equiv {C C' : Type} [Fintype C] [Fintype C'] (φ : C ≃ C') (P' : C' → ℝ)
    (h : P' ∈ stdSimplex ℝ C') : (P' ∘ φ) ∈ stdSimplex ℝ C := by
  refine ⟨fun c => h.1 _, ?_⟩
  have := Equiv.sum_comp φ P'
  simp only [Function.comp]
  rw [this]
  exact h.2

theorem comparison_equiv {V V' C C' : Type} [Fintype C] [Fintype C'] (D : PMF ℕ+)
    (E : Election V C) (E' : Election V' C') (φ : C ≃ C') (ψ : V ≃ V')
    (hψ : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b)
    (P' : C' → ℝ) (hP : P' ∈ stdSimplex ℝ C') (v : V) (c : C) :
    comparison D E' P' (ψ v) (φ c) = comparison D E (P' ∘ φ) v c := by
  rw [comparison_eq D E' _ _ P' hP, comparison_eq D E _ _ _ (simplex_equiv φ P' hP),
    leftRank_equiv E E' φ ψ hψ]
  rfl

theorem score_equiv {V V' C C' : Type} [Fintype V] [Fintype V'] [Fintype C] [Fintype C']
    (D : PMF ℕ+) (E : Election V C) (E' : Election V' C') (φ : C ≃ C') (ψ : V ≃ V')
    (hψ : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b)
    (P' : C' → ℝ) (hP : P' ∈ stdSimplex ℝ C') (c : C) :
    score D E' P' (φ c) = score D E (P' ∘ φ) c := by
  unfold score voterMean
  rw [Fintype.card_congr ψ.symm, ← Equiv.sum_comp ψ]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  exact comparison_equiv D E E' φ ψ hψ P' hP v c

theorem stable_equiv {V V' C C' : Type} [Fintype V] [Fintype V'] [Fintype C] [Fintype C']
    (D : PMF ℕ+) (E : Election V C) (E' : Election V' C') (φ : C ≃ C') (ψ : V ≃ V')
    (hψ : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b)
    (P' : C' → ℝ) (h : IsStable D E' P') : IsStable D E (P' ∘ φ) := by
  refine ⟨simplex_equiv φ P' h.1, fun c => ?_⟩
  rw [← score_equiv D E E' φ ψ hψ P' h.1]
  exact h.2 _

theorem notDist_equiv {V V' C C' : Type} [Fintype V] [Fintype V'] [Fintype C] [Fintype C']
    (E : Election V C) (E' : Election V' C') (φ : C ≃ C') (ψ : V ≃ V')
    (hψ : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b)
    (P' : C' → ℝ) (B : ℝ) (h : ¬ HasDistortionAtMost E (P' ∘ φ) B) :
    ¬ HasDistortionAtMost E' P' B := by
  intro hd
  apply h
  intro d hd1 hd2 a
  let m : V' ⊕ C' → V ⊕ C := Sum.map ψ.symm φ.symm
  let d' : V' ⊕ C' → V' ⊕ C' → ℝ := fun x y => d (m x) (m y)
  have hp : IsPseudometric d' :=
    ⟨fun x y => hd1.nonneg _ _, fun x => hd1.self _, fun x y => hd1.symm _ _,
      fun x y z => hd1.triangle _ _ _⟩
  have hc : Consistent E' d' := by
    intro v' a' b' hab
    have := hd2 (ψ.symm v') (φ.symm a') (φ.symm b') (by
      rw [← hψ]; simpa using hab)
    simpa [d', m] using this
  have hcc : ∀ a : C, candCost d' (φ a) = candCost d a := by
    intro a
    unfold candCost voterMean
    rw [Fintype.card_congr ψ.symm, ← Equiv.sum_comp ψ.symm]
    simp [d', m]
  have := hd d' hp hc (φ a)
  unfold lotteryCost at this ⊢
  rw [← Equiv.sum_comp φ] at this
  simpa [hcc] using this

end RandomSizeStable.Dev.T2b
end

section
set_option autoImplicit false

open PctDistortion StableVotingDistortion

namespace RandomSizeStable.Dev.T2c

open Classical in
/-- the half-unit offset of voter `v`: `0` iff `o` is her top choice. -/
noncomputable def delta {V C : Type} (E : Election V C) (o : C) (v : V) : ℝ :=
  if ∀ c, c ≠ o → E.prefers v o c then 0 else 1 / 2

open Classical in
/-- distance from voter `v` to candidate `c`. -/
noncomputable def d0 {V C : Type} (E : Election V C) (o : C) (v : V) (c : C) : ℝ :=
  delta E o v + if E.prefers v o c then 1 else 0

open Classical in
noncomputable def dC {C : Type} (c c' : C) : ℝ := if c = c' then 0 else 1

open Classical in
/-- the `ℓ∞` metric built from the profile `f`. -/
noncomputable def dd {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C) :
    V ⊕ C → V ⊕ C → ℝ :=
  fun x y => Finset.univ.sup' Finset.univ_nonempty (fun c'' =>
    |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') x) -
      (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y)|)

theorem delta_nonneg {V C : Type} (E : Election V C) (o : C) (v : V) : 0 ≤ delta E o v := by
  unfold delta; split_ifs <;> norm_num

theorem d0_nonneg {V C : Type} (E : Election V C) (o : C) (v : V) (c : C) : 0 ≤ d0 E o v c := by
  unfold d0
  have := delta_nonneg E o v
  split_ifs <;> linarith

theorem d0_le_one_add {V C : Type} (E : Election V C) (o : C) (v : V) (c : C) :
    d0 E o v c ≤ delta E o v + 1 := by
  unfold d0; split_ifs <;> linarith

theorem sup_le_helper {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C)
    (x y : V ⊕ C) (c'' : C) :
    |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') x) -
      (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y)| ≤ dd E o x y := by
  unfold dd
  exact Finset.le_sup' (fun c'' => |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') x) -
      (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y)|) (Finset.mem_univ c'')

theorem dd_le {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C)
    (x y : V ⊕ C) (r : ℝ)
    (h : ∀ c'', |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') x) -
      (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y)| ≤ r) : dd E o x y ≤ r := by
  unfold dd
  exact Finset.sup'_le _ _ (fun c'' _ => h c'')

theorem dd_pseudo {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C) :
    IsPseudometric (dd E o) := by
  have hnn : ∀ x y, 0 ≤ dd E o x y := fun x y => by
    obtain ⟨c⟩ := (inferInstance : Nonempty C)
    exact le_trans (abs_nonneg _) (sup_le_helper E o x y c)
  refine ⟨hnn, fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
  · exact le_antisymm (dd_le E o x x 0 (fun c'' => by simp)) (hnn x x)
  · apply le_antisymm
    · exact dd_le E o x y _ (fun c'' => by
        rw [abs_sub_comm]; exact sup_le_helper E o y x c'')
    · exact dd_le E o y x _ (fun c'' => by
        rw [abs_sub_comm]; exact sup_le_helper E o x y c'')
  · refine dd_le E o x z _ (fun c'' => ?_)
    calc _ ≤ |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') x) -
          (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y)| +
        |(Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') y) -
          (Sum.elim (fun v => d0 E o v c'') (fun c => dC c c'') z)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (sup_le_helper E o x y c'') (sup_le_helper E o y z c'')

theorem dd_vc {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C) (v : V) (c : C) :
    dd E o (Sum.inl v) (Sum.inr c) = d0 E o v c := by
  classical
  apply le_antisymm
  · refine dd_le E o _ _ _ (fun c'' => ?_)
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h0 := d0_nonneg E o v c
    have h1 := d0_nonneg E o v c''
    -- T1 and T1'
    have T1 : d0 E o v c'' ≤ d0 E o v c + dC c c'' := by
      unfold dC; split_ifs with h
      · subst h; simp
      · have := d0_le_one_add E o v c''
        unfold d0 at h0 ⊢
        split_ifs <;> linarith [delta_nonneg E o v]
    have T1' : dC c c'' ≤ d0 E o v c + d0 E o v c'' := by
      unfold dC; split_ifs with h
      · exact add_nonneg h0 h1
      · unfold d0
        by_cases hd : ∀ x, x ≠ o → E.prefers v o x
        · have hdel : delta E o v = 0 := by unfold delta; exact if_pos hd
          rw [hdel]
          by_cases hc : c = o
          · subst hc
            have := hd c'' (Ne.symm h)
            simp [this]
            split_ifs <;> norm_num
          · have := hd c hc
            simp [this]
            split_ifs <;> norm_num
        · have hdel : delta E o v = 1 / 2 := by unfold delta; exact if_neg hd
          rw [hdel]
          split_ifs <;> norm_num
    rw [abs_le]
    constructor <;> linarith
  · have := sup_le_helper E o (Sum.inl v) (Sum.inr c) c
    simp only [Sum.elim_inl, Sum.elim_inr, dC, if_true, sub_zero] at this
    exact le_trans (le_abs_self _) this

theorem consistent_dd {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (o : C) :
    Consistent E (dd E o) := by
  classical
  intro v a b hab
  rw [dd_vc, dd_vc]
  have hs := E.isStrictTotalOrder v
  unfold d0
  by_cases h : E.prefers v o a
  · have h2 : E.prefers v o b := trans_of (E.prefers v) h hab
    simp [h, h2]
  · by_cases h2 : E.prefers v o b <;> simp [h, h2]

open Classical in
theorem candCost_dd {V C : Type} [Fintype V] [Fintype C] [Nonempty C] (E : Election V C)
    (o : C) (c : C) :
    candCost (dd E o) c = voterMean (fun v => delta E o v) +
      voterMean (fun v => if E.prefers v o c then (1 : ℝ) else 0) := by
  classical
  unfold candCost voterMean
  simp only [dd_vc, d0, Finset.sum_add_distrib]
  ring

end RandomSizeStable.Dev.T2c
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common RandomSizeStable.Dev.T2b
open scoped Classical
set_option linter.unusedSectionVars false

namespace RandomSizeStable.Dev.T2d

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

theorem score_convexOn {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (c : C) :
    ConvexOn ℝ (stdSimplex ℝ C) (fun P => score D E P c) := by
  refine ⟨convex_stdSimplex ℝ C, ?_⟩
  intro P hP Q hQ a b ha hb hab
  simp only [smul_eq_mul]
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

/-- the number of candidates other than `o`. -/
noncomputable def nH {C : Type} [Fintype C] (o : C) : ℕ := (Finset.univ.filter (· ≠ o)).card

/-- mass `t` uniform on the candidates other than `o`, mass `1 - t` on `o`. -/
noncomputable def Pt {C : Type} [Fintype C] (o : C) (t : ℝ) : C → ℝ :=
  fun c => if c = o then 1 - t else t / nH o

theorem Pt_simplex {C : Type} [Fintype C] (o : C) (hN : 0 < nH o) (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : Pt o t ∈ stdSimplex ℝ C := by
  refine ⟨fun c => ?_, ?_⟩
  · unfold Pt
    have : (0:ℝ) < nH o := by exact_mod_cast hN
    split_ifs
    · linarith
    · positivity
  · have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => c ≠ o) (Pt o t)
    rw [← h]
    have e1 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c ≠ o), Pt o t c = 1 - t := by
      have : Finset.univ.filter (fun c : C => ¬ c ≠ o) = {o} := by
        ext c; simp
      rw [this]; simp [Pt]
    have e2 : ∑ c ∈ Finset.univ.filter (fun c => c ≠ o), Pt o t c = t := by
      rw [Finset.sum_congr rfl (g := fun _ => t / nH o)]
      · simp only [Finset.sum_const, nsmul_eq_mul]
        have : (nH o : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        unfold nH at this ⊢
        field_simp
      · intro c hc
        simp at hc
        simp [Pt, hc]
    rw [e1, e2]; ring

section Sym

variable {V C G : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] [Fintype G]
  (D : PMF ℕ+) (E : Election V C) (o : C) (φ : G → C ≃ C) (ψ : G → V ≃ V)

theorem card_G (hreg : ∀ c, c ≠ o → ∀ F : C → ℝ,
      ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ o), F c')
    (c0 : C) (hc0 : c0 ≠ o) : (Fintype.card G : ℝ) = nH o := by
  have := hreg c0 hc0 (fun _ => 1)
  simpa [nH] using this

theorem Pt_comp (hφo : ∀ g, φ g o = o) (t : ℝ) (g : G) : Pt o t ∘ φ g = Pt o t := by
  ext c
  unfold Pt
  simp only [Function.comp]
  by_cases h : c = o
  · subst h; simp [hφo]
  · have : φ g c ≠ o := by
      intro h'
      apply h
      have := (φ g).injective (h'.trans (hφo g).symm)
      exact this
    simp [h, this]

theorem sym_stable
    (hψ : ∀ g v a b, E.prefers (ψ g v) (φ g a) (φ g b) ↔ E.prefers v a b)
    (hφo : ∀ g, φ g o = o)
    (hreg : ∀ c, c ≠ o → ∀ F : C → ℝ,
      ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ o), F c')
    (hN : 0 < nH o) (Q : C → ℝ) (hQ : IsStable D E Q) :
    IsStable D E (Pt o (∑ c ∈ Finset.univ.filter (· ≠ o), Q c)) := by
  have hex : ∃ c0 : C, c0 ≠ o := by
    by_contra h
    push Not at h
    have : nH o = 0 := by
      unfold nH; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; simpa using h
    omega
  obtain ⟨c0, hc0⟩ := hex
  have hG : (Fintype.card G : ℝ) = nH o := card_G o φ hreg c0 hc0
  have hNpos : (0 : ℝ) < nH o := by exact_mod_cast hN
  have hGpos : 0 < Fintype.card G := by
    have : (0 : ℝ) < Fintype.card G := by rw [hG]; exact hNpos
    exact_mod_cast this
  have : Nonempty G := Fintype.card_pos_iff.1 hGpos
  set q := ∑ c ∈ Finset.univ.filter (· ≠ o), Q c with hq
  have hQo : Q o = 1 - q := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => c ≠ o) Q
    have e1 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c ≠ o), Q c = Q o := by
      have : Finset.univ.filter (fun c : C => ¬ c ≠ o) = {o} := by
        ext c; simp
      rw [this]; simp
    rw [e1, hQ.1.2] at h
    rw [hq]; linarith
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun c _ => hQ.1.1 c)
  have hq1 : q ≤ 1 := by
    have := hQ.1.1 o
    linarith
  -- the symmetrised lottery
  set Pbar : C → ℝ := ∑ g, (1 / (Fintype.card G : ℝ)) • (Q ∘ φ g) with hPbar
  have hPeq : Pbar = Pt o q := by
    ext c
    rw [hPbar, Finset.sum_apply]
    simp only [Pi.smul_apply, Function.comp, smul_eq_mul]
    by_cases h : c = o
    · subst h
      simp only [hφo, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold Pt
      simp only [if_true, hQo]
      field_simp
    · rw [← Finset.mul_sum, hreg c h (fun c' => Q c')]
      unfold Pt
      simp only [h, if_false, hG]
      ring
  have hstab : ∀ g, IsStable D E (Q ∘ φ g) := fun g => stable_equiv D E E (φ g) (ψ g) (hψ g) Q hQ
  have hw : (∑ _g : G, (1 / (Fintype.card G : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [← hPeq]
  refine ⟨?_, fun c => ?_⟩
  · rw [hPeq]
    exact Pt_simplex o hN q hq0 hq1
  · have hj := (score_convexOn D E c).map_sum_le (t := Finset.univ)
      (w := fun _ => 1 / (Fintype.card G : ℝ)) (p := fun g => Q ∘ φ g)
      (fun g _ => by positivity) hw (fun g _ => (hstab g).1)
    simp only [smul_eq_mul] at hj
    refine le_trans hj ?_
    have : ∀ g, score D E (Q ∘ φ g) c ≤ benchmark D := fun g => (hstab g).2 c
    calc _ ≤ ∑ g : G, (1 / (Fintype.card G : ℝ)) * benchmark D :=
          Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (this g) (by positivity))
      _ = benchmark D := by
          rw [← Finset.sum_mul, hw, one_mul]

theorem exists_ne (hN : 0 < nH o) : ∃ c0 : C, c0 ≠ o := by
  by_contra h
  push Not at h
  have : nH o = 0 := by
    unfold nH; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; simpa using h
  omega

theorem sum_split (F : C → ℝ) :
    ∑ c, F c = F o + ∑ c ∈ Finset.univ.filter (· ≠ o), F c := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => c ≠ o) F
  have e1 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c ≠ o), F c = F o := by
    have : Finset.univ.filter (fun c : C => ¬ c ≠ o) = {o} := by
      ext c; simp
    rw [this]; simp
  rw [← h, e1]; ring

theorem sum_ne (F : C → ℝ) :
    ∑ c ∈ Finset.univ.filter (· ≠ o), F c = ∑ c, F c - F o := by
  rw [sum_split o F]; ring

theorem P1_scores
    (hψ : ∀ g v a b, E.prefers (ψ g v) (φ g a) (φ g b) ↔ E.prefers v a b)
    (hφo : ∀ g, φ g o = o)
    (hreg : ∀ c, c ≠ o → ∀ F : C → ℝ,
      ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ o), F c')
    (hN : 0 < nH o) (c : C) (hc : c ≠ o) :
    score D E (Pt o 1) c = benchmark D := by
  obtain ⟨c0, hc0⟩ := exists_ne o hN
  have hP1 : Pt o 1 ∈ stdSimplex ℝ C := Pt_simplex o hN 1 zero_le_one le_rfl
  have hall : ∀ c, c ≠ o → score D E (Pt o 1) c = score D E (Pt o 1) c0 := by
    intro c hc
    have h := hreg c0 hc0 (fun x => if x = c then (1:ℝ) else 0)
    have h2 : ∑ c' ∈ Finset.univ.filter (· ≠ o), (if c' = c then (1:ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']
      simp [hc]
    rw [h2] at h
    obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [h]; exact one_ne_zero)
    have hgc : φ g c0 = c := by
      by_contra hne
      exact hg (by simp [hne])
    rw [← hgc, score_equiv D E E (φ g) (ψ g) (hψ g) _ hP1, Pt_comp o φ hφo]
  have hsum := score_avg D E (Pt o 1) hP1
  rw [sum_split o] at hsum
  have e1 : Pt o 1 o = 0 := by simp [Pt]
  have hNr : (nH o : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e2 : ∑ c ∈ Finset.univ.filter (· ≠ o), Pt o 1 c * score D E (Pt o 1) c =
      score D E (Pt o 1) c0 := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 / (nH o : ℝ)) * score D E (Pt o 1) c0)]
    · simp only [Finset.sum_const, nsmul_eq_mul]
      unfold nH at hNr ⊢
      field_simp
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rw [hall c hc]
      simp [Pt, hc]
  rw [e1, zero_mul, zero_add, e2] at hsum
  rw [hall c hc]; exact hsum

theorem key
    (hψ : ∀ g v a b, E.prefers (ψ g v) (φ g a) (φ g b) ↔ E.prefers v a b)
    (hφo : ∀ g, φ g o = o)
    (hreg : ∀ c, c ≠ o → ∀ F : C → ℝ,
      ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ o), F c')
    (hN : 0 < nH o) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hlt : score D E (Pt o p) o < benchmark D) (Q : C → ℝ) (hQ : IsStable D E Q) :
    p ≤ ∑ c ∈ Finset.univ.filter (· ≠ o), Q c := by
  by_contra hqp
  push Not at hqp
  set q := ∑ c ∈ Finset.univ.filter (· ≠ o), Q c with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun c _ => hQ.1.1 c)
  have hq1 : q < 1 := lt_of_lt_of_le hqp hp1
  have hPq : IsStable D E (Pt o q) := sym_stable D E o φ ψ hψ hφo hreg hN Q hQ
  have hP1 : Pt o 1 ∈ stdSimplex ℝ C := Pt_simplex o hN 1 zero_le_one le_rfl
  have hNr : (0 : ℝ) < nH o := by exact_mod_cast hN
  have step : ∀ t, q ≤ t → t < 1 → benchmark D ≤ score D E (Pt o t) o := by
    intro t hqt ht1
    have h1q : 0 < 1 - q := by linarith
    have hPt : Pt o t = ((1 - t) / (1 - q)) • Pt o q + ((t - q) / (1 - q)) • Pt o 1 := by
      ext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      unfold Pt
      by_cases h : c = o
      · simp only [h, if_true]; field_simp; ring
      · simp only [h, if_false]; field_simp; ring
    have hab : (1 - t) / (1 - q) + (t - q) / (1 - q) = 1 := by field_simp; ring
    have hle : ∀ c, c ≠ o → score D E (Pt o t) c ≤ benchmark D := by
      intro c hc
      rw [hPt]
      have := (score_convexOn D E c).2 hPq.1 hP1 (div_nonneg (by linarith) h1q.le)
        (div_nonneg (by linarith) h1q.le) hab
      simp only [smul_eq_mul] at this
      refine le_trans this ?_
      rw [P1_scores D E o φ ψ hψ hφo hreg hN c hc]
      have := hPq.2 c
      have h3 := mul_le_mul_of_nonneg_left this
        (div_nonneg (show 0 ≤ 1 - t by linarith) h1q.le)
      have h4 : ((1 - t) / (1 - q) + (t - q) / (1 - q)) * benchmark D = benchmark D := by
        rw [hab, one_mul]
      linarith
    have hPtS : Pt o t ∈ stdSimplex ℝ C := Pt_simplex o hN t (by linarith) ht1.le
    have hsum := score_avg D E (Pt o t) hPtS
    rw [sum_split o] at hsum
    have e1 : Pt o t o = 1 - t := by simp [Pt]
    have e2 : ∑ c ∈ Finset.univ.filter (· ≠ o), Pt o t c * score D E (Pt o t) c ≤
        t * benchmark D := by
      calc _ ≤ ∑ c ∈ Finset.univ.filter (· ≠ o), (t / nH o) * benchmark D := by
            apply Finset.sum_le_sum
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
            have : Pt o t c = t / nH o := by simp [Pt, hc]
            rw [this]
            exact mul_le_mul_of_nonneg_left (hle c hc) (by
              have : (0:ℝ) ≤ t := by linarith
              positivity)
        _ = t * benchmark D := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            unfold nH at hNr ⊢
            field_simp
    rw [e1] at hsum
    have : (1 - t) * benchmark D ≤ (1 - t) * score D E (Pt o t) o := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  -- closure
  have hmaps : Set.MapsTo (Pt o) (Set.Icc (0:ℝ) 1) (stdSimplex ℝ C) :=
    fun t ht => Pt_simplex o hN t ht.1 ht.2
  have hPc : Continuous (Pt o) := by
    apply continuous_pi
    intro c
    unfold Pt
    split_ifs <;> fun_prop
  have hcont : ContinuousOn (fun t => score D E (Pt o t) o) (Set.Icc (0:ℝ) 1) :=
    (score_contOn D E o).comp hPc.continuousOn hmaps
  have hS : IsClosed (Set.Icc q 1 ∩ (fun t => score D E (Pt o t) o) ⁻¹' Set.Ici (benchmark D)) :=
    (hcont.mono (Set.Icc_subset_Icc hq0 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
  have hsub : Set.Ico q 1 ⊆ Set.Icc q 1 ∩ (fun t => score D E (Pt o t) o) ⁻¹' Set.Ici (benchmark D) :=
    fun t ht => ⟨⟨ht.1, ht.2.le⟩, step t ht.1 ht.2⟩
  have hcl := closure_minimal hsub hS
  rw [closure_Ico hq1.ne] at hcl
  have := (hcl ⟨hqp.le, hp1⟩).2
  exact absurd hlt (not_lt.2 this)

theorem key'
    (hψ : ∀ g v a b, E.prefers (ψ g v) (φ g a) (φ g b) ↔ E.prefers v a b)
    (hφo : ∀ g, φ g o = o)
    (hreg : ∀ c, c ≠ o → ∀ F : C → ℝ,
      ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ o), F c')
    (hN : 0 < nH o) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hlt : score D E (Pt o p) o < benchmark D) (Q : C → ℝ) (hQ : IsStable D E Q) :
    p ≤ 1 - Q o := by
  have := key D E o φ ψ hψ hφo hreg hN p hp0 hp1 hlt Q hQ
  rw [sum_ne o Q, hQ.1.2] at this
  exact this

end Sym

end RandomSizeStable.Dev.T2d
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common RandomSizeStable.Dev.T2b RandomSizeStable.Dev.T2c
  RandomSizeStable.Dev.T2d
open scoped Classical

namespace RandomSizeStable.Dev.T2e

theorem cnt_lt (n m : ℕ) (h : m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < m)).card = m := by
  have := Fin.card_filter_val_lt (n := n) (m := m)
  simpa [min_eq_right h] using this

theorem cnt_ge (n m : ℕ) (h : m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => m ≤ i.val)).card = n - m := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => i.val < m)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h1
  rw [cnt_lt n m h] at h1
  omega

/-- number of `H`-members above `o` for voter group `u`. -/
def jv (N k zn : ℕ) {zd : ℕ} (u : Fin zd) : ℕ := if u.val < zn then N - k else 0

def pos {N : ℕ} [NeZero N] (s i : Fin N) : ℕ := (i - s).val

/-- ranking keys: smaller is better. -/
def key {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (s : Fin N) (u : Fin zd) :
    Option (Fin N) → ℕ
  | none => jv N k zn u
  | some i => if pos s i < jv N k zn u then pos s i else pos s i + 1

theorem key_inj {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (s : Fin N) (u : Fin zd)
    (a b : Option (Fin N)) (h : key k zn s u a = key k zn s u b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i => simp only [key] at h; split_ifs at h <;> omega
  | some i =>
    cases b with
    | none => simp only [key] at h; split_ifs at h <;> omega
    | some i' =>
      simp only [key] at h
      have : pos s i = pos s i' := by split_ifs at h <;> omega
      unfold pos at this
      have := Fin.ext this
      rw [sub_left_inj] at this
      rw [this]

/-- the symmetric profile. -/
def Eprof {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) :
    Election (Fin N × Fin zd) (Option (Fin N)) where
  prefers w a b := key k zn w.1 w.2 a < key k zn w.1 w.2 b
  isStrictTotalOrder w :=
    { trichotomous := fun a b h1 h2 =>
        key_inj k zn _ _ _ _ (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
      irrefl := fun a => lt_irrefl _
      trans := fun a b c => lt_trans }

def φ {N : ℕ} [NeZero N] (g : Fin N) : Option (Fin N) ≃ Option (Fin N) :=
  Equiv.optionCongr (Equiv.addRight g)

def ψ {N : ℕ} [NeZero N] {zd : ℕ} (g : Fin N) : (Fin N × Fin zd) ≃ (Fin N × Fin zd) :=
  Equiv.prodCongr (Equiv.addRight g) (Equiv.refl _)

theorem key_equiv {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (g s : Fin N) (u : Fin zd)
    (a : Option (Fin N)) : key k zn (s + g) u (φ g a) = key k zn s u a := by
  cases a with
  | none => simp [φ, key]
  | some i =>
    simp only [φ, Equiv.optionCongr_apply, Option.map_some, Equiv.coe_addRight, key, pos,
      add_sub_add_right_eq_sub]
    exact if_congr Iff.rfl rfl rfl

theorem hψ {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (g : Fin N) (w : Fin N × Fin zd)
    (a b : Option (Fin N)) :
    (Eprof (N := N) (zd := zd) k zn).prefers (ψ g w) (φ g a) (φ g b) ↔
      (Eprof (N := N) (zd := zd) k zn).prefers w a b := by
  simp only [Eprof, ψ, Equiv.prodCongr_apply, Prod.map, Equiv.coe_addRight, Equiv.refl_apply,
    key_equiv]

theorem hφo {N : ℕ} [NeZero N] (g : Fin N) : φ g none = none := by simp [φ]

theorem hreg {N : ℕ} [NeZero N] (c : Option (Fin N)) (hc : c ≠ none) (F : Option (Fin N) → ℝ) :
    ∑ g, F (φ g c) = ∑ c' ∈ Finset.univ.filter (· ≠ none), F c' := by
  obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.1 hc
  have h1 : ∑ g, F (φ g (some i)) = ∑ j : Fin N, F (some j) := by
    have := Equiv.sum_comp (Equiv.addLeft i) (fun j : Fin N => F (some j))
    rw [← this]
    simp [φ, add_comm]
  rw [h1, Finset.sum_filter, Fintype.sum_option]
  simp

theorem nH_eq {N : ℕ} [NeZero N] : nH (none : Option (Fin N)) = N := by
  unfold nH
  rw [Finset.card_filter, Fintype.sum_option]
  simp

theorem jv_le {N zd : ℕ} (k zn : ℕ) (u : Fin zd) : jv N k zn u ≤ N := by
  unfold jv; split_ifs <;> omega

theorem prefers_none_some {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (s : Fin N) (u : Fin zd)
    (i : Fin N) :
    (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none (some i) ↔ jv N k zn u ≤ pos s i := by
  simp only [Eprof, key]
  split_ifs <;> omega

theorem sum_shift {N : ℕ} [NeZero N] (s : Fin N) (j : ℕ) (hj : j ≤ N) (x : ℝ) :
    ∑ i : Fin N, (if j ≤ (i - s).val then x else 0) = ((N - j : ℕ) : ℝ) * x := by
  have := Equiv.sum_comp (Equiv.subRight s) (fun i : Fin N => if j ≤ i.val then x else 0)
  simp only [Equiv.subRight_apply] at this
  rw [this, ← Finset.sum_filter, Finset.sum_const, cnt_ge N j hj]
  simp

theorem sum_shift' {N : ℕ} [NeZero N] (i : Fin N) (j : ℕ) (hj : j ≤ N) (x : ℝ) :
    ∑ s : Fin N, (if j ≤ (i - s).val then x else 0) = ((N - j : ℕ) : ℝ) * x := by
  have := Equiv.sum_comp (Equiv.subLeft i) (fun s : Fin N => if j ≤ s.val then x else 0)
  simp only [Equiv.subLeft_apply] at this
  rw [this, ← Finset.sum_filter, Finset.sum_const, cnt_ge N j hj]
  simp

theorem sum_u {zd : ℕ} (zn : ℕ) (hzn : zn ≤ zd) (A B : ℝ) :
    ∑ u : Fin zd, (if u.val < zn then A else B) = zn * A + ((zd - zn : ℕ) : ℝ) * B := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, cnt_lt zd zn hzn]
  have : (Finset.univ.filter (fun u : Fin zd => ¬ u.val < zn)).card = zd - zn := by
    have := cnt_ge zd zn hzn
    simpa only [not_lt] using this
  rw [this]
  simp

theorem leftRank_o {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (t : ℝ) (s : Fin N) (u : Fin zd) :
    leftRank (Eprof (N := N) (zd := zd) k zn) (Pt (none : Option (Fin N)) t) (s, u) none =
      ((N - jv N k zn u : ℕ) : ℝ) * (t / N) := by
  unfold leftRank
  rw [Finset.sum_filter, Fintype.sum_option]
  have h0 : ¬ (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none none := by
    simp [Eprof]
  simp only [h0, if_false, zero_add]
  have : ∀ i : Fin N, (if (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none (some i) then
      Pt (none : Option (Fin N)) t (some i) else 0) =
      if jv N k zn u ≤ (i - s).val then t / N else 0 := by
    intro i
    have e : Pt (none : Option (Fin N)) t (some i) = t / N := by
      simp [Pt, nH_eq]
    rw [e]
    exact if_congr (prefers_none_some k zn s u i) rfl rfl
  simp only [this]
  exact sum_shift s _ (jv_le k zn u) _

theorem comparison_eq_Sc {V C : Type} [Fintype C] (D : PMF ℕ+) (E : Election V C) (v : V) (c : C)
    (P : C → ℝ) :
    comparison D E P v c = RandomSizeStable.Dev.T2a.Sc D (leftRank E P v c) (P c) := by
  unfold comparison RandomSizeStable.Dev.T2a.Sc RandomSizeStable.Dev.T2a.J
  congr 1; ext k
  rw [sum_draws_eq]

theorem card_W {N zd : ℕ} : (Fintype.card (Fin N × Fin zd) : ℝ) = (N : ℝ) * zd := by
  simp

theorem Nsub_cast {N : ℕ} (k zn : ℕ) (hk : k ≤ N) {zd : ℕ} (u : Fin zd) :
    ((N - jv N k zn u : ℕ) : ℝ) = if u.val < zn then (k : ℝ) else (N : ℝ) := by
  unfold jv
  split_ifs
  · rw [Nat.sub_sub_self hk]
  · simp

theorem score_o {N : ℕ} [NeZero N] {zd : ℕ} (D : PMF ℕ+) (k zn : ℕ) (hk : k ≤ N)
    (hzn : zn ≤ zd) (hzd : 0 < zd) (t : ℝ) :
    score D (Eprof (N := N) (zd := zd) k zn) (Pt (none : Option (Fin N)) t) none =
      ((zn : ℝ) / zd) * RandomSizeStable.Dev.T2a.Sc D ((k : ℝ) / N * t) (1 - t) +
        (1 - (zn : ℝ) / zd) * RandomSizeStable.Dev.T2a.Sc D t (1 - t) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hzd' : (zd : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hzd.ne'
  unfold score voterMean
  rw [card_W]
  have h1 : ∀ (s : Fin N) (u : Fin zd), comparison D (Eprof (N := N) (zd := zd) k zn)
      (Pt (none : Option (Fin N)) t) (s, u) none =
      if u.val < zn then RandomSizeStable.Dev.T2a.Sc D ((k : ℝ) / N * t) (1 - t)
        else RandomSizeStable.Dev.T2a.Sc D t (1 - t) := by
    intro s u
    rw [comparison_eq_Sc, leftRank_o, Nsub_cast k zn hk u]
    have e : Pt (none : Option (Fin N)) t none = 1 - t := by simp [Pt]
    rw [e]
    split_ifs
    · congr 1; ring
    · congr 1; field_simp
  rw [Fintype.sum_prod_type]
  simp only [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_u zn hzn, Nat.cast_sub hzn]
  field_simp

theorem delta_eq {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (hk : k < N) (s : Fin N) (u : Fin zd) :
    delta (Eprof (N := N) (zd := zd) k zn) none (s, u) = if u.val < zn then 1 / 2 else 0 := by
  unfold delta
  by_cases hu : u.val < zn
  · have hj : jv N k zn u = N - k := by simp [jv, hu]
    have : ¬ ∀ c, c ≠ none → (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none c := by
      intro h
      have := h (some s) (by simp)
      rw [prefers_none_some] at this
      unfold pos at this
      simp only [sub_self, Fin.val_zero] at this
      omega
    rw [if_neg this, if_pos hu]
  · have hj : jv N k zn u = 0 := by simp [jv, hu]
    have : ∀ c, c ≠ none → (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none c := by
      intro c hc
      obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.1 hc
      rw [prefers_none_some, hj]
      exact Nat.zero_le _
    rw [if_pos this, if_neg hu]

theorem voterMean_delta {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (hk : k < N) (hzn : zn ≤ zd)
    (hzd : 0 < zd) :
    voterMean (fun w => delta (Eprof (N := N) (zd := zd) k zn) none w) =
      (zn : ℝ) / (2 * zd) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hzd' : (zd : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hzd.ne'
  unfold voterMean
  rw [card_W]
  rw [Fintype.sum_prod_type]
  simp only [delta_eq k zn hk]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_u zn hzn]
  field_simp
  simp

theorem voterMean_W {N : ℕ} [NeZero N] {zd : ℕ} (k zn : ℕ) (hk : k ≤ N) (hzn : zn ≤ zd)
    (hzd : 0 < zd) (i : Fin N) :
    voterMean (fun w => if (Eprof (N := N) (zd := zd) k zn).prefers w none (some i)
      then (1 : ℝ) else 0) = ((zn : ℝ) / zd) * ((k : ℝ) / N) + (1 - (zn : ℝ) / zd) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hzd' : (zd : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hzd.ne'
  unfold voterMean
  rw [card_W]
  rw [Fintype.sum_prod_type_right]
  have h1 : ∀ u : Fin zd, ∑ s : Fin N, (if (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none
      (some i) then (1 : ℝ) else 0) = if u.val < zn then (k : ℝ) else (N : ℝ) := by
    intro u
    have : ∀ s : Fin N, (if (Eprof (N := N) (zd := zd) k zn).prefers (s, u) none (some i)
        then (1 : ℝ) else 0) = if jv N k zn u ≤ (i - s).val then 1 else 0 := by
      intro s
      exact if_congr (prefers_none_some k zn s u i) rfl rfl
    simp only [this]
    rw [sum_shift' i _ (jv_le k zn u), Nsub_cast k zn hk u, mul_one]
  simp only [h1]
  rw [sum_u zn hzn, Nat.cast_sub hzn]
  field_simp

end RandomSizeStable.Dev.T2e
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory PctDistortion StableVotingDistortion RandomSizeStable.Stability
  RandomSizeStable.Dev.Common RandomSizeStable.Dev.T2b RandomSizeStable.Dev.T2c
  RandomSizeStable.Dev.T2d RandomSizeStable.Dev.T2e
open scoped Classical

namespace RandomSizeStable.Dev.T2f

theorem model_main {N : ℕ} [NeZero N] {zd : ℕ} (D : PMF ℕ+) (k zn : ℕ) (hkN : k < N)
    (hzn0 : 0 < zn) (hzn : zn ≤ zd) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hscore : ((zn : ℝ) / zd) * RandomSizeStable.Dev.T2a.Sc D ((k : ℝ) / N * p) (1 - p) +
      (1 - (zn : ℝ) / zd) * RandomSizeStable.Dev.T2a.Sc D p (1 - p) < benchmark D)
    (hdist : (71 / 125 : ℝ) * ((zn : ℝ) / zd) <
      p * (((zn : ℝ) / zd) * ((k : ℝ) / N) + (1 - (zn : ℝ) / zd)))
    (Q : Option (Fin N) → ℝ) (hQ : IsStable D (Eprof (N := N) (zd := zd) k zn) Q) :
    ¬ HasDistortionAtMost (Eprof (N := N) (zd := zd) k zn) Q (267 / 125) := by
  have hzd : 0 < zd := lt_of_lt_of_le hzn0 hzn
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : Nonempty (Fin N × Fin zd) := ⟨(⟨0, hNpos⟩, ⟨0, hzd⟩)⟩
  have hN : 0 < nH (none : Option (Fin N)) := by rw [nH_eq]; exact hNpos
  have hlt : score D (Eprof (N := N) (zd := zd) k zn) (Pt none p) none < benchmark D := by
    rw [score_o D k zn hkN.le hzn hzd]; exact hscore
  have hkey := key' D (Eprof (N := N) (zd := zd) k zn) none (φ (N := N)) (ψ (N := N) (zd := zd))
    (fun g v a b => hψ k zn g v a b) (fun g => hφo g)
    (fun c hc F => by convert hreg c hc F) hN p hp0 hp1 hlt Q hQ
  intro h
  have hd := h _ (dd_pseudo (Eprof (N := N) (zd := zd) k zn) none)
    (consistent_dd (Eprof (N := N) (zd := zd) k zn) none) none
  set E := Eprof (N := N) (zd := zd) k zn with hE
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hzdr : (0 : ℝ) < zd := by exact_mod_cast hzd
  have hznr : (zn : ℝ) ≤ zd := by exact_mod_cast hzn
  set z : ℝ := (zn : ℝ) / zd with hz
  set wH : ℝ := z * ((k : ℝ) / N) + (1 - z) with hwH
  have hz1 : z ≤ 1 := by rw [hz, div_le_one hzdr]; exact hznr
  have hz0 : 0 ≤ z := by positivity
  have hwH0 : 0 ≤ wH := by
    have : 0 ≤ (k : ℝ) / N := by positivity
    rw [hwH]; nlinarith
  have hδ := voterMean_delta (N := N) (zd := zd) k zn hkN hzn hzd
  have hδ' : voterMean (fun w => delta E none w) = z / 2 := by
    rw [hδ, hz]; field_simp
  have hcc : ∀ c, candCost (dd E none) c = z / 2 +
      (if c = none then 0 else wH) := by
    intro c
    rw [candCost_dd, hδ']
    congr 1
    cases c with
    | none =>
      have : ∀ w : Fin N × Fin zd, ¬ E.prefers w none none := by
        intro w; simp [hE, Eprof]
      simp [this, voterMean]
    | some i =>
      rw [voterMean_W k zn hkN.le hzn hzd i]
      simp [hwH, hz]
  have hlot : lotteryCost (dd E none) Q = z / 2 + wH * (1 - Q none) := by
    unfold lotteryCost
    rw [sum_split none]
    rw [Finset.sum_congr rfl (g := fun c => Q c * (z / 2 + wH)) (fun c hc => ?_)]
    · rw [← Finset.sum_mul, sum_ne none Q, hQ.1.2, hcc none]
      simp only [if_true, add_zero]
      ring
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rw [hcc c]; simp [hc]
  rw [hlot, hcc none] at hd
  simp only [if_true, add_zero] at hd
  have : wH * p ≤ wH * (1 - Q none) := mul_le_mul_of_nonneg_left hkey hwH0
  nlinarith

end RandomSizeStable.Dev.T2f
end

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Dev.T2

open RandomSizeStable.Stability RandomSizeStable.Dev.T2a RandomSizeStable.Dev.T2b
  RandomSizeStable.Dev.T2e RandomSizeStable.Dev.T2f

theorem assemble (D : PMF ℕ+) (N k : ℕ) (hkN : k < N) (p z0 : ℝ) (hp0 : 0 < p) (hz0 : 0 < z0)
    (hz1 : z0 ≤ 1)
    (hcal : (71 / 125 : ℝ) * z0 = p * (z0 * ((k : ℝ) / N) + (1 - z0)))
    (hlt : z0 * Sc D ((k : ℝ) / N * p) (1 - p) + (1 - z0) * Sc D p (1 - p) < benchmark D) :
    ∃ zd zn : ℕ, 0 < zn ∧ zn ≤ zd ∧
      ((zn : ℝ) / zd) * Sc D ((k : ℝ) / N * p) (1 - p) +
        (1 - (zn : ℝ) / zd) * Sc D p (1 - p) < benchmark D ∧
      (71 / 125 : ℝ) * ((zn : ℝ) / zd) <
        p * (((zn : ℝ) / zd) * ((k : ℝ) / N) + (1 - (zn : ℝ) / zd)) := by
  obtain ⟨zn, zd, h1, h2, h3, h4⟩ := exists_rat_z _ _ _ z0 hz0 hlt
  have hzd : (0 : ℝ) < zd := by exact_mod_cast h2
  refine ⟨zd, zn, h1, ?_, h4, ?_⟩
  · have : (zn : ℝ) / zd < 1 := lt_of_lt_of_le h3 hz1
    rw [div_lt_one hzd] at this
    exact_mod_cast this.le
  · have hr0 : 0 ≤ (k : ℝ) / N := by positivity
    have hr1 : (k : ℝ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hkN))]
      exact_mod_cast hkN.le
    set r := (k : ℝ) / N
    set z := (zn : ℝ) / zd
    have hpos : 0 < p - p * r + 71 / 125 := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h3) hpos]

theorem exists_params (D : PMF ℕ+) :
    ∃ (N : ℕ) (k : ℕ) (zd zn : ℕ) (p : ℝ), 0 < N ∧ k < N ∧ 0 < zn ∧ zn ≤ zd ∧ 0 < p ∧ p ≤ 1 ∧
      ((zn : ℝ) / zd) * Sc D ((k : ℝ) / N * p) (1 - p) +
        (1 - (zn : ℝ) / zd) * Sc D p (1 - p) < benchmark D ∧
      (71 / 125 : ℝ) * ((zn : ℝ) / zd) <
        p * (((zn : ℝ) / zd) * ((k : ℝ) / N) + (1 - (zn : ℝ) / zd)) := by
  by_cases h : pgf D (71 / 125) < benchmark D
  · obtain ⟨zd, zn, h1, h2, h3, h4⟩ := assemble D 125 71 (by norm_num) 1 1 one_pos one_pos le_rfl
      (by norm_num) (by
        have e : ((71 : ℕ) : ℝ) / ((125 : ℕ) : ℝ) * 1 = 71 / 125 := by norm_num
        rw [e, sub_self, Sc_zero]
        simpa using h)
    exact ⟨125, 71, zd, zn, 1, by norm_num, by norm_num, h1, h2, one_pos, le_rfl, h3, h4⟩
  · push Not at h
    have hB := caseB D h
    obtain ⟨zd, zn, h1, h2, h3, h4⟩ := assemble D 39 1 (by norm_num) (3 / 4)
      ((3 / 4 : ℝ) / (3 / 4 + 71 / 125 - 1 / 52)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by
        have e : ((1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ) * (3 / 4) = 1 / 52 := by norm_num
        have e2 : (1 : ℝ) - 3 / 4 = 1 / 4 := by norm_num
        rw [e, e2]
        exact hB)
    exact ⟨39, 1, zd, zn, 3 / 4, by norm_num, by norm_num, h1, h2, by norm_num, by norm_num,
      h3, h4⟩

/-- pull an election back along maps of voters and candidates. -/
def comapE {V V' C C' : Type} (E : Election V C) (f : V' → V) (g : C' ≃ C) :
    Election V' C' where
  prefers v a b := E.prefers (f v) (g a) (g b)
  isStrictTotalOrder v :=
    { trichotomous := fun a b h1 h2 => g.injective ((E.isStrictTotalOrder (f v)).trichotomous
        (g a) (g b) h1 h2)
      irrefl := fun a => (E.isStrictTotalOrder (f v)).irrefl (g a)
      trans := fun a b c => (E.isStrictTotalOrder (f v)).trans (g a) (g b) (g c) }

theorem part2 (D : PMF ℕ+) :
    ∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m) (E : Election (Fin n) (Fin m)),
      ∀ P : Fin m → ℝ, IsStable D E P → ¬ HasDistortionAtMost E P (267 / 125) := by
  obtain ⟨N, k, zd, zn, p, hN, hkN, hzn0, hzn, hp0, hp1, hsc, hdist⟩ := exists_params D
  haveI : NeZero N := ⟨hN.ne'⟩
  have hzd : 0 < zd := lt_of_lt_of_le hzn0 hzn
  let E : Election (Fin N × Fin zd) (Option (Fin N)) := Eprof k zn
  let ψ : (Fin N × Fin zd) ≃ Fin (N * zd) := finProdFinEquiv
  let φ : Option (Fin N) ≃ Fin (N + 1) := (finSuccEquiv N).symm
  let E' : Election (Fin (N * zd)) (Fin (N + 1)) := comapE E ψ.symm φ.symm
  have hψ' : ∀ v a b, E'.prefers (ψ v) (φ a) (φ b) ↔ E.prefers v a b := by
    intro v a b
    simp [E', comapE]
  refine ⟨N * zd, N + 1, Nat.mul_pos hN hzd, Nat.succ_pos N, E', fun P hP => ?_⟩
  exact notDist_equiv E E' φ ψ hψ' P (267 / 125)
    (model_main D k zn hkN hzn0 hzn p hp0 hp1 hsc hdist _
      (stable_equiv D E E' φ ψ hψ' P hP))

end RandomSizeStable.Dev.T2

namespace RandomSizeStable

open RandomSizeStable.Stability in
/-- Theorem 2, pp.5 and 16: for every positive-integer draw law `D` (any PMF on ℕ+,
infinite support and infinite mean allowed), chosen BEFORE the profile, there is a finite
nonempty unweighted profile on which EVERY random-size stable lottery for `D` has metric
distortion strictly greater than 267/125 = 2.136; hence every rule that always returns an
RSL_D has distortion strictly greater than 267/125.
"Distortion strictly greater than B" (B ≥ 1, with the 0/0 = 1, z/0 = +∞ conventions of
Definition 1, p.8) is `¬ HasDistortionAtMost E P B`: some consistent pseudometric and
some candidate `a` with `cost(P) > B · cost(a)`. -/
theorem chk_theorem_2 (D : PMF ℕ+) :
    (267 / 125 : ℝ) = 2.136 ∧
    (∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m) (E : Election (Fin n) (Fin m)),
      ∀ P : Fin m → ℝ, IsStable D E P → ¬ HasDistortionAtMost E P (267 / 125)) ∧
    (∀ R : VotingRule,
      (∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        IsStable D E (R n m hn hm E).val) →
      ∃ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        ¬ HasDistortionAtMost E (R n m hn hm E).val (267 / 125)) := by
  have h2 := RandomSizeStable.Dev.T2.part2 D
  refine ⟨by norm_num, h2, fun R hR => ?_⟩
  obtain ⟨n, m, hn, hm, E, hE⟩ := h2
  exact ⟨n, m, hn, hm, E, hE _ (hR n m hn hm E)⟩

end RandomSizeStable

end

theorem solution : type_of% @RandomSizeStable.chk_theorem_2 := @RandomSizeStable.chk_theorem_2
