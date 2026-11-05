-- Prove2me | solution 2 for VarianceRegularization.Covering.robust_minimizer_oracle_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T22:31:33.937038+00:00
-- url     : https://prove2.me/submissions/6323b0c3-94af-455b-abf1-97f46f1c769d

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup
import Definitions.Def_VarianceRegularization_Covering_empCoveringNumber

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace CexF47

/-- `ω₁` as a type: uncountable, every initial segment countable. -/
def Y : Type := (Cardinal.aleph.{0} 1).ord.ToType

noncomputable instance : LinearOrder Y :=
  inferInstanceAs (LinearOrder (Cardinal.aleph.{0} 1).ord.ToType)

set_option linter.deprecated false in
theorem Y_Iio_countable (y : Y) : (Set.Iio y).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one]
  exact Cardinal.mk_Iio_toType_ord_lt (c := Cardinal.aleph.{0} 1) y

theorem Y_Iic_countable (y : Y) : (Set.Iic y).Countable := by
  rw [← Set.Iio_union_right]
  exact (Y_Iio_countable y).union (Set.countable_singleton y)

theorem Y_not_countable : ¬ (Set.univ : Set Y).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Cardinal.mk_univ]
  have : Cardinal.mk Y = Cardinal.aleph.{0} 1 := by
    show Cardinal.mk (Cardinal.aleph.{0} 1).ord.ToType = _
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  rw [this]
  exact lt_irrefl _

theorem Y_bound (S : Set Y) (hS : S.Countable) : ∃ z, ∀ y ∈ S, y < z := by
  have hU : (⋃ y ∈ S, Set.Iic y).Countable := hS.biUnion fun y _ => Y_Iic_countable y
  obtain ⟨z, hz⟩ : ∃ z, z ∉ ⋃ y ∈ S, Set.Iic y := by
    by_contra h
    push_neg at h
    exact Y_not_countable (hU.mono fun x _ => h x)
  refine ⟨z, fun y hy => ?_⟩
  by_contra hle
  exact hz (Set.mem_biUnion hy (not_lt.mp hle))

/-- The countable–cocountable σ-algebra. -/
instance : MeasurableSpace Y where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl s h := by
    rcases h with h | h
    · right; simpa using h
    · left; exact h
  measurableSet_iUnion f hf := by
    by_cases h : ∀ i, (f i).Countable
    · exact Or.inl (Set.countable_iUnion h)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      right
      refine ((hf i).resolve_left hi).mono ?_
      exact Set.compl_subset_compl.mpr (Set.subset_iUnion f i)

open Classical in
/-- The `0`–`1` measure: countable sets get `0`, cocountable sets get `1`. -/
noncomputable def muY : Measure Y :=
  Measure.ofMeasurable (fun s _ => if s.Countable then 0 else 1) (by simp)
    (by
      intro f hf hdisj
      by_cases h : ∀ i, (f i).Countable
      · rw [if_pos (Set.countable_iUnion h)]
        simp [h]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have hU : ¬ (⋃ j, f j).Countable := fun hc => hi (hc.mono (Set.subset_iUnion f i))
        rw [if_neg hU]
        have hco : (f i)ᶜ.Countable := (hf i).resolve_left hi
        have hother : ∀ j, j ≠ i → (f j).Countable := by
          intro j hj
          exact hco.mono (fun x hx => Set.disjoint_left.mp (hdisj hj) hx)
        rw [tsum_eq_single i]
        · simp [hi]
        · intro j hj
          simp [hother j hj])

theorem muY_apply_countable (s : Set Y) (hs : s.Countable) : muY s = 0 := by
  have hm : MeasurableSet s := Or.inl hs
  rw [muY, Measure.ofMeasurable_apply s hm, if_pos hs]

instance : IsProbabilityMeasure muY := by
  constructor
  rw [muY, Measure.ofMeasurable_apply Set.univ MeasurableSet.univ, if_neg Y_not_countable]

/-- `f_q = 1` strictly above `q`, `0` on the countable null segment `Iic q`. -/
noncomputable def fq (q : Y) : Y → ℝ := Set.indicator (Set.Ioi q) (fun _ => (1 : ℝ))

def G : Set (Y → ℝ) := Set.range fq

theorem Ioi_meas (q : Y) : MeasurableSet (Set.Ioi q) := by
  right
  rw [Set.compl_Ioi]
  exact Y_Iic_countable q

theorem G_hyp : ∀ f ∈ G, Measurable f ∧ ∀ x, f x ∈ Set.Icc (0:ℝ) 1 := by
  rintro f ⟨q, rfl⟩
  refine ⟨measurable_const.indicator (Ioi_meas q), fun x => ?_⟩
  unfold fq
  by_cases hx : x ∈ Set.Ioi q
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem integral_fq (q : Y) : ∫ x, fq q x ∂muY = 1 := by
  unfold fq
  rw [integral_indicator_const _ (Ioi_meas q), smul_eq_mul, mul_one, measureReal_def]
  have h1 : muY (Set.Ioi q) = 1 := by
    have hc : muY (Set.Iic q) = 0 := muY_apply_countable _ (Y_Iic_countable q)
    have := prob_compl_eq_one_sub (μ := muY) (s := Set.Iic q)
      (Or.inl (Y_Iic_countable q))
    rw [Set.compl_Iic, hc, tsub_zero] at this
    exact this
  rw [h1]
  simp

/-- The evaluation set of `G` at any `m` points has at most `m + 1` elements. -/
theorem evalSet_sub {m : ℕ} (x : Fin m → Y) :
    VarianceRegularization.Covering.evalSet G x ⊆
      insert (fun _ => (1:ℝ)) (Set.range fun j : Fin m => fun i => fq (x j) (x i)) := by
  rintro v ⟨f, ⟨q, rfl⟩, rfl⟩
  by_cases hS : ∃ i, x i ≤ q
  · obtain ⟨i0, hi0⟩ := hS
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun i => x i ≤ q) x ⟨i0, by simp [hi0]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hjmax
    right
    refine ⟨j, funext fun i => ?_⟩
    dsimp only
    unfold fq
    by_cases hi : x i ≤ q
    · have h1 : x i ∉ Set.Ioi (x j) := by simpa using hjmax i hi
      have h2 : x i ∉ Set.Ioi q := by simpa using hi
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    · have h2 : x i ∈ Set.Ioi q := by simpa using hi
      have h1 : x i ∈ Set.Ioi (x j) := lt_of_le_of_lt hj (by simpa using hi)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · push_neg at hS
    left
    funext i
    dsimp only
    unfold fq
    rw [Set.indicator_of_mem (show x i ∈ Set.Ioi q from hS i)]

open VarianceRegularization.Covering VarianceRegularization.Expansion in
theorem robustSup_zero (n : ℕ) (ρ : ℝ) : robustSup n ρ (fun _ => (0:ℝ)) = 0 := by
  unfold robustSup
  apply le_antisymm
  · apply Real.sSup_nonpos
    rintro _ ⟨p, _, rfl⟩
    simp
  · apply Real.sSup_nonneg
    rintro _ ⟨p, _, rfl⟩
    simp

open VarianceRegularization.Covering VarianceRegularization.Expansion in
theorem robustSup_nonneg (n : ℕ) (ρ : ℝ) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ robustSup n ρ z := by
  unfold robustSup
  apply Real.sSup_nonneg
  rintro _ ⟨p, hp, rfl⟩
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hz i)

/-- The class: the chain together with the zero function. -/
def F0 : Set (Y → ℝ) := insert 0 G

theorem F0_ne : F0.Nonempty := ⟨0, Set.mem_insert _ _⟩

theorem F0_hyp : ∀ f ∈ F0, Measurable f ∧ ∀ x, f x ∈ Set.Icc (0:ℝ) 1 := by
  intro f hf
  rcases hf with rfl | hf
  · exact ⟨measurable_const, fun _ => ⟨le_refl _, zero_le_one⟩⟩
  · exact G_hyp f hf

theorem iInf_le_zero (ρ : ℝ) (n : ℕ) :
    (⨅ f : F0, (∫ x, (f : Y → ℝ) x ∂muY
      + 2 * Real.sqrt (2 * ρ / n * variance (f : Y → ℝ) muY))) ≤ 0 := by
  have hbdd : BddBelow (Set.range fun f : F0 => ∫ x, (f : Y → ℝ) x ∂muY
      + 2 * Real.sqrt (2 * ρ / n * variance (f : Y → ℝ) muY)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact add_nonneg (integral_nonneg fun x => ((F0_hyp f f.2).2 x).1)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  refine (ciInf_le hbdd ⟨0, Set.mem_insert _ _⟩).trans ?_
  simp

open VarianceRegularization.Covering in
/-- Every sample lies below some chain point `z`; `fq z` vanishes on the sample, so it is a
robust minimizer (robust risk `0`), while its mean is `1`. -/
theorem event (n : ℕ) (t ρ ε : ℝ)
    (hnum : 19 * (1 - 0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε < 1)
    (s : Fin n → Y) :
    ∃ g ∈ F0, (∀ f ∈ F0, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
      (⨅ f : F0, (∫ x, (f : Y → ℝ) x ∂muY
          + 2 * Real.sqrt (2 * ρ / n * variance (f : Y → ℝ) muY)))
        + 19 * (1 - 0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
        < ∫ x, g x ∂muY := by
  obtain ⟨z, hz⟩ := Y_bound (Set.range s) (Set.countable_range s)
  refine ⟨fq z, Set.mem_insert_of_mem _ ⟨z, rfl⟩, ?_, ?_⟩
  · intro f hf
    have h0 : (fun i => fq z (s i)) = fun _ => (0:ℝ) := by
      funext i
      unfold fq
      rw [Set.indicator_of_notMem]
      simpa using (hz (s i) ⟨i, rfl⟩).le
    unfold robustRisk
    rw [h0, robustSup_zero]
    exact robustSup_nonneg _ _ _ fun i => ((F0_hyp f hf).2 (s i)).1
  · rw [integral_fq]
    have := iInf_le_zero ρ n
    linarith

theorem numeric : 19 * (1 - 0) * (180:ℝ) / (3 * ((10000 : ℕ) : ℝ))
    + (2 + 4 * Real.sqrt (2 * 20 / ((10000 : ℕ) : ℝ))) * (1 / 100) < 1 := by
  have : ((10000 : ℕ) : ℝ) = 10000 := by norm_num
  rw [this]
  have hs : Real.sqrt (2 * 20 / 10000 : ℝ) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 * 20 / 10000 : ℝ)]

theorem evalSet_sub0 {m : ℕ} (x : Fin m → Y) :
    VarianceRegularization.Covering.evalSet F0 x ⊆
      insert (fun _ => (0:ℝ)) (insert (fun _ => (1:ℝ))
        (Set.range fun j : Fin m => fun i => fq (x j) (x i))) := by
  rintro v ⟨f, hf, rfl⟩
  rcases hf with rfl | hf
  · left; rfl
  · exact Or.inr (evalSet_sub x ⟨f, hf, rfl⟩)

theorem cover_le (m : ℕ) (ε : ℝ) :
    VarianceRegularization.Covering.empCoveringNumber F0 ε m ≤ (m + 2 : ℕ) := by
  unfold VarianceRegularization.Covering.empCoveringNumber
  refine iSup_le fun x => ?_
  refine (Metric.coveringNumber_le_encard_self _).trans ?_
  refine (Set.encard_le_encard (evalSet_sub0 x)).trans ?_
  refine (Set.encard_insert_le _ _).trans ?_
  have h : (Set.range fun j : Fin m => fun i => fq (x j) (x i)).encard
      ≤ (Set.univ : Set (Fin m)).encard := by
    rw [← Set.image_univ]
    exact Set.encard_image_le _ _
  have hc : (Set.univ : Set (Fin m)).encard = m := by simp
  have h2 := Set.encard_insert_le (Set.range fun j : Fin m => fun i => fq (x j) (x i))
    (fun _ => (1:ℝ))
  calc _ ≤ (Set.range fun j : Fin m => fun i => fq (x j) (x i)).encard + 1 + 1 := by gcongr
    _ ≤ (m : ℕ∞) + 1 + 1 := by rw [← hc]; gcongr
    _ = ((m + 2 : ℕ) : ℕ∞) := by push_cast; ring

theorem exp20 : (2:ℝ) ^ 20 ≤ Real.exp 20 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have : Real.exp 20 = Real.exp 1 ^ 20 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  exact pow_le_pow_left₀ (by norm_num) h2 20

theorem bound_lt :
    2 * (3 * (((2 * 10000 + 2 : ℕ) : ℕ∞) : ENNReal) + 1) * ENNReal.ofReal (Real.exp (-20)) < 1 := by
  have hc : 2 * (3 * (((2 * 10000 + 2 : ℕ) : ℕ∞) : ENNReal) + 1) = ENNReal.ofReal 120014 := by
    rw [ENat.toENNReal_coe, show (120014 : ℝ) = ((120014 : ℕ) : ℝ) by norm_num,
      ENNReal.ofReal_natCast]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_lt_one, Real.exp_neg]
  have h1 := exp20
  have hp : 0 < Real.exp 20 := Real.exp_pos 20
  rw [← div_eq_mul_inv, div_lt_one hp]
  norm_num at h1 ⊢
  linarith

end CexF47

open MeasureTheory ProbabilityTheory VarianceRegularization.Covering in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (F : Set (X → ℝ)) (hFne : F.Nonempty) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ρ ε : ℝ)
    (hnt : 8 * (M1 - M0) ^ 2 / t ≤ n) (ht : Real.log 12 ≤ t) (hε : 0 < ε) (hρ : 9 * t ≤ ρ),
    Measure.pi (fun _ : Fin n => P)
        {s | ∃ g ∈ F, (∀ f ∈ F, robustRisk ρ g s ≤ robustRisk ρ f s) ∧
          (⨅ f : F, (∫ x, (f : X → ℝ) x ∂P
              + 2 * Real.sqrt (2 * ρ / n * variance (f : X → ℝ) P)))
            + 19 * (M1 - M0) * ρ / (3 * n) + (2 + 4 * Real.sqrt (2 * t / n)) * ε
            < ∫ x, g x ∂P}
      ≤ 2 * (3 * (empCoveringNumber F ε (2 * n) : ENNReal) + 1)
          * ENNReal.ofReal (Real.exp (-t))) := by
  intro h
  have h2 := h (X := CexF47.Y) CexF47.muY CexF47.F0 CexF47.F0_ne 0 1 zero_le_one CexF47.F0_hyp
    10000 (by norm_num) 20 180 (1 / 100) (by norm_num)
    ((Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)) (by norm_num) (by norm_num)
  have h3 : (Measure.pi fun _ : Fin 10000 => CexF47.muY) Set.univ
      ≤ 2 * (3 * (empCoveringNumber CexF47.F0 (1 / 100) (2 * 10000) : ENNReal) + 1)
        * ENNReal.ofReal (Real.exp (-20)) := by
    refine le_trans (measure_mono ?_) h2
    intro s _
    exact CexF47.event 10000 20 180 (1 / 100) CexF47.numeric s
  rw [measure_univ] at h3
  have h4 : 2 * (3 * (empCoveringNumber CexF47.F0 (1 / 100) (2 * 10000) : ENNReal) + 1)
        * ENNReal.ofReal (Real.exp (-20))
      ≤ 2 * (3 * (((2 * 10000 + 2 : ℕ) : ℕ∞) : ENNReal) + 1) * ENNReal.ofReal (Real.exp (-20)) := by
    gcongr
    exact CexF47.cover_le (2 * 10000) (1 / 100)
  exact absurd (h3.trans h4) (not_le.mpr CexF47.bound_lt)
