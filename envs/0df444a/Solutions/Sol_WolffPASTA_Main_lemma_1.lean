-- Prove2me | solution 1 for WolffPASTA.Main.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:39:40.896977+00:00
-- url     : https://prove2.me/submissions/fd6af013-2992-4703-9df9-0c057e677171

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting
import Theorems.Thm_WolffPASTA_Main_eq_6

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Nat
open WolffPASTA.Main

namespace WolffPASTAAux



lemma pois_term_succ (r : ℝ) (n : ℕ) :
    Real.exp (-r) * r ^ (n + 1) / ((n + 1)! : ℝ) * ((n + 1 : ℕ) : ℝ)
      = r * (Real.exp (-r) * r ^ n / (n ! : ℝ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have : (n ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasSum_pois_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ)) (r : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  refine h.congr_fun (fun n => ?_)
  exact pois_term_succ r n

lemma hasSum_pois_sq (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := ((hasSum_pois_mean r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have key : (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ (n + 1) / ((n + 1) ! : ℝ)
      * (((n + 1 : ℕ) : ℝ)) ^ 2) = fun i : ℕ => (r:ℝ) * (Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)
        * (i : ℝ) + Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)) := by
    funext n
    have e := pois_term_succ (r:ℝ) n
    rw [pow_two, ← mul_assoc, e]
    push_cast
    ring
  have hv : (r:ℝ) + (r:ℝ) ^ 2 - ∑ i ∈ Finset.range 1,
      Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ) * (i : ℝ) ^ 2 = (r:ℝ) * ((r:ℝ) + 1) := by
    simp; ring
  rw [hv, key]
  exact h


lemma pois_integral_id (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_mean r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_mean r).tsum_eq

lemma pois_integral_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = r + (r : ℝ) ^ 2 := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_sq r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_sq r).tsum_eq


lemma T_nonneg {Ω : Type*} (A : ℝ → Ω → ℕ) (k : ℕ) (ω : Ω) : 0 ≤ T A k ω :=
  Real.sInf_nonneg (fun _ hx => hx.1)

lemma T_measurable {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℕ)
    (hmeas : ∀ t, Measurable (A t)) (hmono : ∀ ω, Monotone (fun t => A t ω)) (k : ℕ) :
    Measurable (T A k) := by
  refine measurable_of_Iio (fun x => ?_)
  have hset : T A k ⁻¹' Set.Iio x =
      (⋃ q : ℚ, {ω | 0 ≤ (q:ℝ) ∧ (q:ℝ) < x ∧ k ≤ A q ω}) ∪
        ({ω | ∀ n : ℕ, A n ω < k} ∩ {_ω | 0 < x}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq,
      Set.mem_inter_iff]
    have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ k ≤ A s ω} := ⟨0, fun _ hs => hs.1⟩
    constructor
    · intro hT
      by_cases hne : ({s : ℝ | 0 ≤ s ∧ k ≤ A s ω}).Nonempty
      · obtain ⟨s, hs, hsx⟩ := (csInf_lt_iff hbdd hne).1 hT
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsx
        left
        exact ⟨q, le_trans hs.1 hq1.le, hq2, le_trans hs.2 (hmono ω hq1.le)⟩
      · right
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have h0 : T A k ω = 0 := by simp only [T]; rw [hne, Real.sInf_empty]
        refine ⟨fun n => ?_, by rw [← h0]; exact hT⟩
        by_contra hc
        push_neg at hc
        have : (n:ℝ) ∈ ({s : ℝ | 0 ≤ s ∧ k ≤ A s ω}) := ⟨by positivity, hc⟩
        rw [hne] at this; exact this
    · rintro (⟨q, hq0, hqx, hqk⟩ | ⟨hall, hx⟩)
      · exact lt_of_le_of_lt (csInf_le hbdd ⟨hq0, hqk⟩) hqx
      · have hne : {s : ℝ | 0 ≤ s ∧ k ≤ A s ω} = ∅ := by
          ext s
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
          intro hs
          exact lt_of_le_of_lt (hmono ω (Nat.le_ceil s)) (hall _)
        have h0 : T A k ω = 0 := by simp only [T]; rw [hne, Real.sInf_empty]
        rw [h0]; exact hx
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_) ?_
  · have : {ω | 0 ≤ (q:ℝ) ∧ (q:ℝ) < x ∧ k ≤ A q ω} =
        {_ω | 0 ≤ (q:ℝ) ∧ (q:ℝ) < x} ∩ (A q ⁻¹' Set.Ici k) := by
      ext ω; simp [and_assoc]
    rw [this]
    exact (MeasurableSet.const _).inter (hmeas _ measurableSet_Ici)
  · refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    have : {ω | ∀ n : ℕ, A n ω < k} = ⋂ n : ℕ, (A n ⁻¹' Set.Iio k) := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun n => hmeas _ measurableSet_Iio

lemma Y_measurable {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℕ)
    (hmeas : ∀ t, Measurable (A t)) (hmono : ∀ ω, Monotone (fun t => A t ω))
    (U : ℝ → Ω → ℝ) (hjoint : JointlyMeasurable U) (s : ℝ) :
    Measurable (Y U A s) := by
  have hj : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
  have hg : ∀ k, Measurable (fun ω => U (T A k ω) ω) := by
    intro k
    have : Measurable (fun ω => ((ω, ⟨T A k ω, Set.mem_Ici.mpr (T_nonneg A k ω)⟩) :
        Ω × Set.Ici (0:ℝ))) :=
      measurable_id.prodMk (T_measurable A hmeas hmono k).subtype_mk
    exact hj.comp this
  have hF : Measurable (fun p : Ω × ℕ => ∑ k ∈ Finset.Icc 1 p.2, U (T A k p.1) p.1) := by
    apply measurable_from_prod_countable_left
    intro m
    show Measurable (fun ω => ∑ k ∈ Finset.Icc 1 m, U (T A k ω) ω)
    exact Finset.measurable_fun_sum (Finset.Icc 1 m) (fun k _ => hg k)
  have hc : Measurable (fun ω => (ω, A s ω)) := measurable_id.prodMk (hmeas s)
  have e : Y U A s = (fun p : Ω × ℕ => ∑ k ∈ Finset.Icc 1 p.2, U (T A k p.1) p.1) ∘
      (fun ω => (ω, A s ω)) := by
    funext ω; simp only [Y, Function.comp]
  rw [e]
  exact hF.comp hc

lemma intU_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hjoint : JointlyMeasurable U) (s : ℝ) (hs : 0 ≤ s) :
    Measurable (fun ω => ∫ r in (0:ℝ)..s, U r ω) := by
  have hj : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
  set H : Ω → ℝ → ℝ := fun ω r => U (max r 0) ω with hH
  have hHm : Measurable (Function.uncurry H) := by
    have : Measurable (fun p : Ω × ℝ => ((p.1, ⟨max p.2 0, Set.mem_Ici.mpr (le_max_right _ _)⟩) :
        Ω × Set.Ici (0:ℝ))) :=
      measurable_fst.prodMk ((measurable_snd.max measurable_const).subtype_mk)
    exact hj.comp this
  have h1 := (hHm.stronglyMeasurable.integral_prod_right
    (ν := (MeasureSpace.volume : Measure ℝ).restrict (Set.Ioc 0 s))).measurable
  convert h1 using 1
  funext ω
  rw [intervalIntegral.integral_of_le hs]
  refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  simp [hH, max_eq_left hr.1.le]

lemma R_measurable {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℕ)
    (hmeas : ∀ t, Measurable (A t)) (hmono : ∀ ω, Monotone (fun t => A t ω))
    (U : ℝ → Ω → ℝ) (hjoint : JointlyMeasurable U) (lam s : ℝ) (hs : 0 ≤ s) :
    Measurable (R U A lam s) := by
  have hV : Measurable (V U s) := measurable_const.mul (intU_measurable U hjoint s hs)
  exact (Y_measurable A hmeas hmono U hjoint s).sub (measurable_const.mul hV)


lemma intU_measurable' {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hjoint : JointlyMeasurable U) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Measurable (fun ω => ∫ r in a..b, U r ω) := by
  have hj : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
  set H : Ω → ℝ → ℝ := fun ω r => U (max r 0) ω with hH
  have hHm : Measurable (Function.uncurry H) := by
    have : Measurable (fun p : Ω × ℝ => ((p.1, ⟨max p.2 0, Set.mem_Ici.mpr (le_max_right _ _)⟩) :
        Ω × Set.Ici (0:ℝ))) :=
      measurable_fst.prodMk ((measurable_snd.max measurable_const).subtype_mk)
    exact hj.comp this
  have h1 := (hHm.stronglyMeasurable.integral_prod_right
    (ν := (MeasureSpace.volume : Measure ℝ).restrict (Set.Ioc a b))).measurable
  convert h1 using 1
  funext ω
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  simp [hH, max_eq_left (le_trans ha hr.1.le)]

/-- The section `s ↦ U(max s 0, ω)` is measurable. -/
lemma section_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hjoint : JointlyMeasurable U) (ω : Ω) :
    Measurable (fun s : ℝ => U (max s 0) ω) := by
  have hm : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
  have hsec : Measurable (fun s : Set.Ici (0 : ℝ) => U s ω) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have : Measurable (fun s : ℝ => (⟨max s 0, Set.mem_Ici.mpr (le_max_right _ _)⟩ :
      Set.Ici (0:ℝ))) :=
    (measurable_id.max measurable_const).subtype_mk
  exact hsec.comp this


/-- The left end point of the grid cell `(a + k h / n, a + (k+1) h / n]` containing `x`. -/
noncomputable def cell (a h : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a + ((⌈(x - a) * n / h⌉₊ : ℝ) - 1) * h / n

lemma cell_bounds (a h : ℝ) (hh : 0 < h) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : a < x) :
    x - h / n ≤ cell a h n x ∧ cell a h n x < x ∧ a ≤ cell a h n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set y := (x - a) * n / h with hy
  have hy0 : 0 < y := by rw [hy]; have : 0 < x - a := by linarith
                         positivity
  have c1 : (⌈y⌉₊ : ℝ) - 1 < y := by
    have := Nat.ceil_lt_add_one hy0.le; linarith
  have c2 : y ≤ ⌈y⌉₊ := Nat.le_ceil y
  have c3 : (1:ℝ) ≤ ⌈y⌉₊ := by
    have : 0 < ⌈y⌉₊ := Nat.ceil_pos.mpr hy0
    exact_mod_cast this
  have e : y * h / n = x - a := by rw [hy]; field_simp
  unfold cell
  refine ⟨?_, ?_, ?_⟩
  · have : (y - 1) * h / n ≤ ((⌈y⌉₊ : ℝ) - 1) * h / n := by
      apply div_le_div_of_nonneg_right _ hn'.le
      exact mul_le_mul_of_nonneg_right (by linarith) hh.le
    have e2 : (y - 1) * h / n = x - a - h / n := by rw [sub_mul, sub_div, e]; ring
    linarith
  · have : ((⌈y⌉₊ : ℝ) - 1) * h / n < y * h / n := by
      apply div_lt_div_of_pos_right _ hn'
      exact mul_lt_mul_of_pos_right c1 hh
    linarith
  · have : (0:ℝ) ≤ ((⌈y⌉₊ : ℝ) - 1) * h / n := by
      apply div_nonneg _ hn'.le
      exact mul_nonneg (by linarith) hh.le
    linarith

lemma cell_eq (a h : ℝ) (hh : 0 < h) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (x : ℝ)
    (h1 : a + k * h / n < x) (h2 : x ≤ a + (k + 1) * h / n) :
    cell a h n x = a + k * h / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hc : ⌈(x - a) * n / h⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · push_cast
      rw [lt_div_iff₀ hh]
      have : k * h / n < x - a := by linarith
      rw [div_lt_iff₀ hn'] at this
      linarith
    · push_cast
      rw [div_le_iff₀ hh]
      have : x - a ≤ (k + 1) * h / n := by linarith
      rw [le_div_iff₀ hn'] at this
      linarith
  unfold cell
  rw [hc]; push_cast; ring

lemma tendsto_cell (a h : ℝ) (hh : 0 < h) (x : ℝ) (hx : a < x) :
    Tendsto (fun n : ℕ => cell a h n x) atTop (𝓝[<] x) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hlow : Tendsto (fun n : ℕ => x - h / n) atTop (𝓝 x) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat h).const_sub x
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (cell_bounds a h hh n hn x hx).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (cell_bounds a h hh n hn x hx).2.1.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (cell_bounds a h hh n hn x hx).2.1


lemma cell_measurable (a h : ℝ) (n : ℕ) : Measurable (cell a h n) := by
  unfold cell
  have : Measurable (fun x : ℝ => ⌈(x - a) * n / h⌉₊) :=
    (((measurable_id.sub_const a).mul_const _).div_const _).nat_ceil
  exact measurable_const.add (((measurable_from_nat.comp this).sub_const 1).mul_const _ |>.div_const _)

lemma T_le_iff {Ω : Type*} (A : ℝ → Ω → ℕ) (ω : Ω) (hmono : Monotone (fun t => A t ω))
    (hrc : ∀ t, ContinuousWithinAt (fun s => (A s ω : ℝ)) (Set.Ici t) t)
    (j : ℕ) (x : ℝ) (hx : 0 ≤ x) (y : ℝ) (hy : 0 ≤ y) (hjy : j ≤ A y ω) :
    T A j ω ≤ x ↔ j ≤ A x ω := by
  have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ j ≤ A s ω} := ⟨0, fun _ hs => hs.1⟩
  constructor
  · intro hT
    by_contra hc
    push_neg at hc
    have hev : ∀ᶠ s in 𝓝[≥] x, (A s ω : ℝ) < A x ω + 1 :=
      (hrc x).eventually (gt_mem_nhds (by linarith))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hge : u ≤ T A j ω := by
      refine le_csInf ⟨y, hy, hjy⟩ (fun s hs => ?_)
      by_contra hsu
      push_neg at hsu
      have hs2 := hs.2
      rcases lt_or_ge s x with hsx | hsx
      · have := hmono hsx.le; simp only at this; omega
      · have h1 : (A s ω : ℝ) < A x ω + 1 := hsub ⟨hsx, hsu⟩
        have h2 : A s ω < A x ω + 1 := by exact_mod_cast h1
        omega
    have : x < u := hu
    linarith
  · intro h
    exact csInf_le hbdd ⟨hx, h⟩

lemma Y_sub_eq {Ω : Type*} (U : ℝ → Ω → ℝ) (A : ℝ → Ω → ℕ) (ω : Ω) (a b : ℝ)
    (hab : A a ω ≤ A b ω) :
    Y U A b ω - Y U A a ω = ∑ j ∈ Finset.Ioc (A a ω) (A b ω), U (T A j ω) ω := by
  have e : ∀ m : ℕ, Finset.Icc 1 m = Finset.Ioc 0 m := fun m => Finset.Icc_add_one_left_eq_Ioc 0 m
  simp only [Y]
  rw [e, e, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hab]
  ring

/-- Pathwise convergence of the grid sums to `Y(t+h) - Y(t)` (left continuity of `U`). -/
lemma Yg_tendsto {Ω : Type*} (A : ℝ → Ω → ℕ) (U : ℝ → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun t => A t ω))
    (hrc : ∀ t, ContinuousWithinAt (fun s => (A s ω : ℝ)) (Set.Ici t) t)
    (t h : ℝ) (ht : 0 ≤ t) (hh : 0 < h)
    (hleft : ∀ s, t < s → ContinuousWithinAt (fun r => U r ω) (Set.Iio s) s) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        U (t + k * h / n) ω * ((A (t + (k + 1) * h / n) ω : ℝ) - A (t + k * h / n) ω))
      atTop (𝓝 (Y U A (t + h) ω - Y U A t ω)) := by
  have hAth : A t ω ≤ A (t + h) ω := hmono (by linarith)
  rw [Y_sub_eq U A ω t (t + h) hAth]
  -- the arrival epochs in `(A t, A (t+h)]` lie in `(t, t + h]`
  have hTj : ∀ j ∈ Finset.Ioc (A t ω) (A (t + h) ω), t < T A j ω ∧ T A j ω ≤ t + h := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    constructor
    · by_contra hc; push_neg at hc
      have := (T_le_iff A ω hmono hrc j t ht (t + h) (by linarith) hj.2).1 hc
      omega
    · exact (T_le_iff A ω hmono hrc j (t + h) (by linarith) (t + h) (by linarith) hj.2).2 hj.2
  have hlim : Tendsto (fun n : ℕ => ∑ j ∈ Finset.Ioc (A t ω) (A (t + h) ω),
      U (cell t h n (T A j ω)) ω) atTop
      (𝓝 (∑ j ∈ Finset.Ioc (A t ω) (A (t + h) ω), U (T A j ω) ω)) := by
    refine tendsto_finset_sum _ (fun j hj => ?_)
    obtain ⟨h1, _⟩ := hTj j hj
    exact (hleft _ h1).tendsto.comp (tendsto_cell t h hh _ h1)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set tk : ℕ → ℝ := fun k => t + k * h / n with htk
  have htk_mono : Monotone tk := by
    intro a b hab
    simp only [htk]
    have : (a:ℝ) ≤ b := by exact_mod_cast hab
    have : (a:ℝ) * h / n ≤ b * h / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hh.le) hn'.le
    linarith
  have htk0 : ∀ k, t ≤ tk k := fun k => by
    simp only [htk]; have : (0:ℝ) ≤ k * h / n := by positivity
    linarith
  -- each cell term
  have hcellsum : ∀ k, U (tk k) ω * ((A (tk (k + 1)) ω : ℝ) - A (tk k) ω) =
      ∑ j ∈ Finset.Ioc (A (tk k) ω) (A (tk (k + 1)) ω), U (cell t h n (T A j ω)) ω := by
    intro k
    have hmk : A (tk k) ω ≤ A (tk (k + 1)) ω := hmono (htk_mono (Nat.le_succ k))
    have heq : ∀ j ∈ Finset.Ioc (A (tk k) ω) (A (tk (k + 1)) ω),
        U (cell t h n (T A j ω)) ω = U (tk k) ω := by
      intro j hj
      rw [Finset.mem_Ioc] at hj
      have hk1 : tk k < T A j ω := by
        by_contra hc; push_neg at hc
        have := (T_le_iff A ω hmono hrc j (tk k) (le_trans ht (htk0 k)) (tk (k + 1))
          (le_trans ht (htk0 _)) hj.2).1 hc
        omega
      have hk2 : T A j ω ≤ tk (k + 1) :=
        (T_le_iff A ω hmono hrc j (tk (k + 1)) (le_trans ht (htk0 _)) (tk (k + 1))
          (le_trans ht (htk0 _)) hj.2).2 hj.2
      have hk2' : T A j ω ≤ t + (k + 1) * h / n := by
        simp only [htk] at hk2; push_cast at hk2; exact hk2
      rw [cell_eq t h hh n hn k _ hk1 hk2']
    rw [Finset.sum_congr rfl heq, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
      Nat.cast_sub hmk]
    ring
  have htel : ∀ m, ∑ k ∈ Finset.range m,
      ∑ j ∈ Finset.Ioc (A (tk k) ω) (A (tk (k + 1)) ω), U (cell t h n (T A j ω)) ω =
      ∑ j ∈ Finset.Ioc (A (tk 0) ω) (A (tk m) ω), U (cell t h n (T A j ω)) ω := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ioc_consecutive _ (hmono (htk_mono (Nat.zero_le _)))
        (hmono (htk_mono (Nat.le_succ m)))
  have e0 : tk 0 = t := by simp [htk]
  have en : tk n = t + h := by simp only [htk]; field_simp
  have hsum : ∑ k ∈ Finset.range n,
      U (t + k * h / n) ω * ((A (t + (k + 1) * h / n) ω : ℝ) - A (t + k * h / n) ω) =
      ∑ k ∈ Finset.range n, U (tk k) ω * ((A (tk (k + 1)) ω : ℝ) - A (tk k) ω) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [htk]; push_cast; ring_nf
  rw [hsum, Finset.sum_congr rfl (fun k _ => hcellsum k), htel n, e0, en]

/-- Left Riemann sums of a bounded measurable function that is left continuous on `(t, ∞)`
converge to its integral over `[t, t + h]`. -/
lemma riemann_tendsto (g : ℝ → ℝ) (hgm : Measurable g) (hg1 : ∀ s, |g s| ≤ 1)
    (t h : ℝ) (hh : 0 < h) (hleft : ∀ s, t < s → ContinuousWithinAt g (Set.Iio s) s) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, g (t + k * h / n) * (h / n)) atTop
      (𝓝 (∫ s in t..(t + h), g s)) := by
  have hgi : ∀ a b : ℝ, ∀ f : ℝ → ℝ, Measurable f → (∀ s, |f s| ≤ 1) →
      IntervalIntegrable f MeasureSpace.volume a b := by
    intro a b f hf hf1
    refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hf.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun s => ?_)
    simp only [Real.norm_eq_abs, abs_one]
    exact hf1 s
  set F : ℕ → ℝ → ℝ := fun n r => g (cell t h n r) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => hgm.comp (cell_measurable t h n)
  have hlim : Tendsto (fun n => ∫ s in t..(t + h), F n s) atTop (𝓝 (∫ s in t..(t + h), g s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall (fun n => (hFm n).aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x _ => ?_)))
      intervalIntegrable_const (Eventually.of_forall (fun x hx => ?_))
    · rw [Real.norm_eq_abs]; exact hg1 _
    · rw [Set.uIoc_of_le (by linarith)] at hx
      exact (hleft x hx.1).tendsto.comp (tendsto_cell t h hh x hx.1)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set tk : ℕ → ℝ := fun k => t + k * h / n with htk
  have hstep : ∀ k, tk k ≤ tk (k + 1) := by
    intro k; simp only [htk]; push_cast
    have : (k:ℝ) * h / n ≤ (k + 1) * h / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hh.le) hn'.le
    linarith
  have hpiece : ∀ k, ∫ s in tk k..tk (k + 1), F n s = g (tk k) * (h / n) := by
    intro k
    have : ∫ s in tk k..tk (k + 1), F n s = ∫ s in tk k..tk (k + 1), g (tk k) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall (fun x hx => ?_))
      rw [Set.uIoc_of_le (hstep k)] at hx
      simp only [hF]
      have h2 : x ≤ t + (k + 1) * h / n := by
        have := hx.2; simp only [htk] at this; push_cast at this; exact this
      rw [cell_eq t h hh n hn k x hx.1 h2]
    rw [this, intervalIntegral.integral_const, smul_eq_mul]
    simp only [htk]; push_cast; ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureSpace.volume)
    (f := F n) (a := tk) (n := n)
    (fun k _ => hgi _ _ (F n) (hFm n) (fun s => hg1 _))
  have e0 : tk 0 = t := by simp [htk]
  have en : tk n = t + h := by simp only [htk]; field_simp
  rw [e0, en] at hsum
  rw [← hsum]
  exact Finset.sum_congr rfl (fun k _ => hpiece k)


/-- Pathwise increment bounds: for `0 ≤ a ≤ b`,
`|R(b) - R(a)| ≤ (A(b) - A(a)) + λ (b - a)` and the same for squares. -/
lemma R_incr_bound {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℕ)
    (hmono : ∀ ω, Monotone (fun t => A t ω)) (lam : ℝ) (hlam : 0 < lam)
    (U : ℝ → Ω → ℝ) (hU : ∀ s ω, 0 ≤ s → 0 ≤ U s ω ∧ U s ω ≤ 1)
    (hjoint : JointlyMeasurable U) (ω : Ω) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (R U A lam b ω - R U A lam a ω) ^ 2 ≤
      (((A b ω - A a ω : ℕ) : ℝ)) ^ 2 + lam ^ 2 * (b - a) ^ 2 ∧
    |R U A lam b ω - R U A lam a ω| ≤ ((A b ω - A a ω : ℕ) : ℝ) + lam * (b - a) := by
  set g : ℝ → ℝ := fun s => U (max s 0) ω with hg
  have hgm : Measurable g := by
    have hm : Measurable (fun p : Ω × Set.Ici (0 : ℝ) => U p.2 p.1) := hjoint
    have hsec : Measurable (fun s : Set.Ici (0 : ℝ) => U s ω) :=
      hm.comp (measurable_const.prodMk measurable_id)
    have : Measurable (fun s : ℝ => (⟨max s 0, Set.mem_Ici.mpr (le_max_right _ _)⟩ :
        Set.Ici (0:ℝ))) :=
      (measurable_id.max measurable_const).subtype_mk
    exact hsec.comp this
  have hg01 : ∀ s, 0 ≤ g s ∧ g s ≤ 1 := fun s => hU _ ω (le_max_right _ _)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g MeasureSpace.volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hgm.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun s => ?_)
    simp only [Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (hg01 s).1]; exact (hg01 s).2
  have hI : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, U s ω = ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le hx] at hs
    simp [hg, max_eq_left hs.1]
  have htV : ∀ x, 0 ≤ x → x * V U x ω = ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    rw [← hI x hx]
    simp only [V]
    rcases hx.lt_or_eq with hx' | hx'
    · field_simp
    · subst hx'; simp
  have hRx : ∀ x, 0 ≤ x → R U A lam x ω = Y U A x ω - lam * ∫ s in (0:ℝ)..x, g s := by
    intro x hx
    simp only [R]
    rw [mul_assoc, htV x hx]
  have hb : 0 ≤ b := le_trans ha hab
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals (hgi 0 a) (hgi a b))
  have hI0 : 0 ≤ ∫ s in a..b, g s := intervalIntegral.integral_nonneg hab (fun s _ => (hg01 s).1)
  have hI1 : ∫ s in a..b, g s ≤ b - a := by
    have := intervalIntegral.integral_mono_on hab (hgi a b) (intervalIntegrable_const (c := (1:ℝ)))
      (fun s _ => (hg01 s).2)
    simpa using this
  -- increments of Y
  have hT : ∀ k, 0 ≤ T A k ω := fun k => Real.sInf_nonneg (fun x hx => hx.1)
  have hAab : A a ω ≤ A b ω := hmono ω hab
  have hsub : Finset.Icc 1 (A a ω) ⊆ Finset.Icc 1 (A b ω) :=
    Finset.Icc_subset_Icc le_rfl hAab
  have hYd : Y U A b ω - Y U A a ω =
      ∑ k ∈ Finset.Icc 1 (A b ω) \ Finset.Icc 1 (A a ω), U (T A k ω) ω := by
    simp only [Y]
    rw [← Finset.sum_sdiff hsub]; ring
  have hY0 : 0 ≤ Y U A b ω - Y U A a ω := by
    rw [hYd]; exact Finset.sum_nonneg (fun k _ => (hU _ ω (hT k)).1)
  have hY1 : Y U A b ω - Y U A a ω ≤ ((A b ω - A a ω : ℕ) : ℝ) := by
    rw [hYd]
    have h1 := Finset.sum_le_card_nsmul (Finset.Icc 1 (A b ω) \ Finset.Icc 1 (A a ω))
      (fun k => U (T A k ω) ω) 1 (fun k _ => (hU _ ω (hT k)).2)
    rw [Finset.card_sdiff_of_subset hsub, Nat.card_Icc, Nat.card_Icc] at h1
    simpa using h1
  rw [hRx b hb, hRx a ha]
  have e : Y U A b ω - lam * (∫ s in (0:ℝ)..b, g s) - (Y U A a ω - lam * ∫ s in (0:ℝ)..a, g s)
      = (Y U A b ω - Y U A a ω) - lam * ∫ s in a..b, g s := by
    rw [← hsplit]; ring
  rw [e]
  set y := Y U A b ω - Y U A a ω
  set I := ∫ s in a..b, g s
  set d : ℝ := ((A b ω - A a ω : ℕ) : ℝ)
  have h1 : 0 ≤ lam * I := mul_nonneg hlam.le hI0
  have h2 : lam * I ≤ lam * (b - a) := mul_le_mul_of_nonneg_left hI1 hlam.le
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  constructor
  · have h3 : (lam * I) ^ 2 ≤ lam ^ 2 * (b - a) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h1 h2 2
    have h4 : y ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hY0 hY1 2
    nlinarith [mul_nonneg hY0 h1]
  · rw [abs_le]; constructor <;> nlinarith


/-- The σ-field of sets that agree `P`-a.s. with a set of `F`. -/
def aeSigma {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure[m0] Ω) (F : MeasurableSpace Ω) :
    MeasurableSpace Ω where
  MeasurableSet' := fun G => ∃ G', MeasurableSet[F] G' ∧ G =ᵐ[P] G'
  measurableSet_empty := ⟨∅, F.measurableSet_empty, EventuallyEq.rfl⟩
  measurableSet_compl := fun G ⟨G', h1, h2⟩ => ⟨G'ᶜ, F.measurableSet_compl _ h1, h2.compl⟩
  measurableSet_iUnion := fun f hf => by
    choose G' hG'm hG'e using hf
    exact ⟨⋃ i, G' i, F.measurableSet_iUnion _ hG'm, Filter.EventuallyEq.countable_iUnion hG'e⟩

lemma measurableSet_aeSigma {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure[m0] Ω)
    (F : MeasurableSpace Ω) (G : Set Ω) :
    MeasurableSet[aeSigma P F] G ↔ ∃ G', MeasurableSet[F] G' ∧ G =ᵐ[P] G' := Iff.rfl

end WolffPASTAAux

open WolffPASTAAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAAJoint P A (U N B)) :
    (∀ t, 0 ≤ t → Integrable (R (U N B) A lam t) P) ∧
      ∀ t h, 0 ≤ t → 0 < h →
        P[fun ω => R (U N B) A lam (t + h) ω - R (U N B) A lam t ω | Rhist (R (U N B) A lam) t]
          =ᵐ[P] 0 := by
  have h6 := eq_6 P N A lam hlam hA B hB hpath hjoint hLAA
  have hP : IsPoissonProcessWithIntensity P A (fun _ => lam) := hA
  have hU : ∀ s ω, 0 ≤ s → 0 ≤ U N B s ω ∧ U N B s ω ≤ 1 := by
    intro s ω _
    simp only [U, Set.indicator]
    split_ifs <;> norm_num
  set W := U N B with hW
  have hWm : ∀ s, 0 ≤ s → Measurable (W s) := by
    intro s hs
    have : W s = Set.indicator {ω | N s ω ∈ B} (fun _ => (1:ℝ)) := by
      funext ω; simp [hW, U, Set.indicator]
    rw [this]; exact measurable_const.indicator (hB s hs)
  have hFle : ∀ r, Fhist A W r ≤ ‹MeasurableSpace Ω› := fun r =>
    iSup₂_le (fun s hs => sup_le (hP.meas s).comap_le (hWm s hs.1).comap_le)
  have hFgen : ∀ r s, s ∈ Set.Icc (0:ℝ) r →
      MeasurableSpace.comap (A s) inferInstance ⊔ MeasurableSpace.comap (W s) inferInstance
        ≤ Fhist A W r := fun r s hs =>
    le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) r) =>
      MeasurableSpace.comap (A s) inferInstance ⊔ MeasurableSpace.comap (W s) inferInstance) s hs
  have hWF : ∀ r s, s ∈ Set.Icc (0:ℝ) r → Measurable[Fhist A W r] (W s) := fun r s hs =>
    (comap_measurable (W s)).mono (le_trans le_sup_right (hFgen r s hs)) le_rfl
  have hAF : ∀ r s, s ∈ Set.Icc (0:ℝ) r → Measurable[Fhist A W r] (A s) := fun r s hs =>
    (comap_measurable (A s)).mono (le_trans le_sup_left (hFgen r s hs)) le_rfl
  have hRm : ∀ s, 0 ≤ s → Measurable (R W A lam s) :=
    fun s hs => R_measurable A hP.meas hP.mono W hjoint lam s hs
  have hR0 : ∀ ω, R W A lam 0 ω = 0 := fun ω => by simp [R, Y, V, hP.zero ω]
  -- Poisson mean
  have hmeanA : ∀ s, 0 ≤ s → Integrable (fun ω => (A s ω : ℝ)) P := by
    intro s hs
    have hAt : (fun ω => A s ω - A 0 ω) = A s := by funext ω; simp [hP.zero ω]
    have hlaw : P.map (A s) = poissonMeasure (lam * s).toNNReal := by
      have := hP.law 0 s le_rfl hs
      rw [hAt] at this
      simpa [intervalIntegral.integral_const, mul_comm] using this
    have h1 := (pois_integral_id (lam * s).toNNReal).1
    rw [← hlaw] at h1
    exact (integrable_map_measure h1.aestronglyMeasurable (hP.meas s).aemeasurable).mp h1
  -- (a) integrability of `R t`
  have hRint : ∀ s, 0 ≤ s → Integrable (R W A lam s) P := by
    intro s hs
    refine ((hmeanA s hs).add (integrable_const (lam * s))).mono' (hRm s hs).aestronglyMeasurable
      (Eventually.of_forall (fun ω => ?_))
    have := (R_incr_bound A hP.mono lam hlam W hU hjoint ω 0 s le_rfl hs).2
    rw [hR0, sub_zero, hP.zero ω, Nat.sub_zero, sub_zero] at this
    rw [Real.norm_eq_abs]; exact this
  refine ⟨hRint, ?_⟩
  intro t h ht hh
  -- `R(t+h) - R(t) = (Y(t+h) - Y(t)) - λ ∫ₜ^{t+h} U`
  set I : Ω → ℝ := fun ω' => ∫ s in t..(t + h), W s ω' with hI
  have hIm : Measurable I := intU_measurable' W hjoint t (t + h) ht (by linarith)
  have hIint : Integrable I P := by
    refine (integrable_const h).mono' hIm.aestronglyMeasurable (Eventually.of_forall (fun ω => ?_))
    have hg := section_measurable W hjoint ω
    have heq : I ω = ∫ s in t..(t + h), W (max s 0) ω := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le (by linarith)] at hs
      simp [max_eq_left (le_trans ht hs.1)]
    have hgi : IntervalIntegrable (fun s => W (max s 0) ω) MeasureSpace.volume t (t + h) := by
      refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hg.aestronglyMeasurable ?_
      refine Eventually.of_forall (fun s => ?_)
      simp only [Real.norm_eq_abs, abs_one]
      rw [abs_of_nonneg (hU _ ω (le_max_right _ _)).1]; exact (hU _ ω (le_max_right _ _)).2
    rw [Real.norm_eq_abs, heq, abs_le]
    constructor
    · have := intervalIntegral.integral_nonneg (μ := MeasureSpace.volume) (a := t) (b := t + h)
        (by linarith) (fun s _ => (hU (max s 0) ω (le_max_right _ _)).1)
      linarith
    · have := intervalIntegral.integral_mono_on (by linarith) hgi
        (intervalIntegrable_const (c := (1:ℝ))) (fun s _ => (hU (max s 0) ω (le_max_right _ _)).2)
      simp at this; linarith
  have hdecomp : ∀ ω, R W A lam (t + h) ω - R W A lam t ω =
      (Y W A (t + h) ω - Y W A t ω) - lam * I ω := by
    intro ω
    have hg := section_measurable W hjoint ω
    have hgi : ∀ a b, IntervalIntegrable (fun s => W (max s 0) ω) MeasureSpace.volume a b := by
      intro a b
      refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hg.aestronglyMeasurable ?_
      refine Eventually.of_forall (fun s => ?_)
      simp only [Real.norm_eq_abs, abs_one]
      rw [abs_of_nonneg (hU _ ω (le_max_right _ _)).1]; exact (hU _ ω (le_max_right _ _)).2
    have hcongr : ∀ a b, 0 ≤ a → a ≤ b →
        ∫ s in a..b, W s ω = ∫ s in a..b, W (max s 0) ω := by
      intro a b ha hab
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le hab] at hs
      simp [max_eq_left (le_trans ha hs.1)]
    have htV : ∀ x, 0 ≤ x → x * V W x ω = ∫ s in (0:ℝ)..x, W s ω := by
      intro x hx
      simp only [V]
      rcases hx.lt_or_eq with hx' | hx'
      · field_simp
      · subst hx'; simp
    simp only [R]
    rw [mul_assoc, mul_assoc, htV _ (by linarith), htV _ ht, hI]
    simp only
    rw [hcongr 0 (t + h) le_rfl (by linarith), hcongr 0 t le_rfl ht,
      hcongr t (t + h) ht (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (hgi 0 t) (hgi t (t + h))]
    ring
  obtain ⟨hYint, hcond⟩ := h6 t h ht hh
  have hDint : Integrable (fun ω => R W A lam (t + h) ω - R W A lam t ω) P :=
    (hRint _ (by linarith)).sub (hRint t ht)
  -- vanishing of the integrals over `ℱₜ`-sets
  have hkey : ∀ G, MeasurableSet[Fhist A W t] G →
      ∫ ω in G, (R W A lam (t + h) ω - R W A lam t ω) ∂P = 0 := by
    intro G hG
    have e1 : ∫ ω in G, (Y W A (t + h) ω - Y W A t ω) ∂P = lam * ∫ ω in G, I ω ∂P := by
      rw [← setIntegral_condExp (hFle t) hYint hG, setIntegral_congr_ae (hFle t G hG)
        (Eventually.of_forall (fun _ _ => rfl)) |>.trans (setIntegral_congr_ae (hFle t G hG)
          (hcond.mono (fun ω hω _ => hω)))]
      rw [integral_const_mul, setIntegral_condExp (hFle t) hIint hG]
    have e2 : (fun ω => R W A lam (t + h) ω - R W A lam t ω) =
        fun ω => (Y W A (t + h) ω - Y W A t ω) - lam * I ω := funext hdecomp
    rw [e2, integral_sub hYint.integrableOn (hIint.const_mul lam).integrableOn,
      integral_const_mul, e1, sub_self]
  -- every `R(s)`, `s ≤ t`, agrees a.s. with an `ℱₜ`-measurable function
  have hmod : ∀ s, s ∈ Set.Icc (0:ℝ) t → AEStronglyMeasurable[Fhist A W t] (R W A lam s) P := by
    intro s hs
    rcases hs.1.lt_or_eq with hs0 | hs0
    · set f : ℕ → Ω → ℝ := fun n ω =>
        (∑ k ∈ Finset.range n, W (0 + k * s / n) ω *
          ((A (0 + (k + 1) * s / n) ω : ℝ) - A (0 + k * s / n) ω)) -
        lam * ∑ k ∈ Finset.range n, W (0 + k * s / n) ω * (s / n) with hf
      have hgrid : ∀ n : ℕ, ∀ k ∈ Finset.range n, (0:ℝ) + k * s / n ∈ Set.Icc (0:ℝ) t ∧
          (0:ℝ) + (k + 1) * s / n ∈ Set.Icc (0:ℝ) t := by
        intro n k hk
        rw [Finset.mem_range] at hk
        have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hk' : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
        have h1 : (k:ℝ) * s / n ≤ s := by
          rw [div_le_iff₀ hn]; nlinarith
        have h2 : ((k:ℝ) + 1) * s / n ≤ s := by
          rw [div_le_iff₀ hn]; nlinarith
        refine ⟨⟨by positivity, by linarith [hs.2]⟩, ⟨by positivity, by linarith [hs.2]⟩⟩
      have hfm : ∀ n, StronglyMeasurable[Fhist A W t] (f n) := by
        intro n
        refine Measurable.stronglyMeasurable ?_
        refine Measurable.sub (Finset.measurable_fun_sum _ (fun k hk => ?_))
          (measurable_const.mul (Finset.measurable_fun_sum _ (fun k hk => ?_)))
        · exact (hWF t _ (hgrid n k hk).1).mul
            ((measurable_from_nat.comp (hAF t _ (hgrid n k hk).2)).sub
              (measurable_from_nat.comp (hAF t _ (hgrid n k hk).1)))
        · exact (hWF t _ (hgrid n k hk).1).mul_const _
      have hlimm : StronglyMeasurable[Fhist A W t]
          (fun ω => limUnder atTop (fun n => f n ω)) := by
        letI : MeasurableSpace Ω := Fhist A W t
        exact StronglyMeasurable.limUnder hfm
      refine ⟨_, hlimm, ?_⟩
      filter_upwards [hpath] with ω hω
      have hY := Yg_tendsto A W ω (hP.mono ω) (hP.rightCont ω) 0 s le_rfl hs0
        (fun r hr => hω.1 r hr)
      set g : ℝ → ℝ := fun r => W (max r 0) ω with hg
      have hgm : Measurable g := section_measurable W hjoint ω
      have hg1 : ∀ r, |g r| ≤ 1 := fun r => by
        rw [abs_of_nonneg (hU _ ω (le_max_right _ _)).1]; exact (hU _ ω (le_max_right _ _)).2
      have hgl : ∀ r, 0 < r → ContinuousWithinAt g (Set.Iio r) r := by
        intro r hr
        refine (hω.1 r hr).congr_of_eventuallyEq ?_ (by simp [hg, max_eq_left hr.le])
        filter_upwards [Ioo_mem_nhdsLT hr] with x hx
        simp [hg, max_eq_left hx.1.le]
      have hRs := riemann_tendsto g hgm hg1 0 s hs0 hgl
      have hRs' : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, W (0 + k * s / n) ω * (s / n))
          atTop (𝓝 (∫ r in (0:ℝ)..s, W r ω)) := by
        have eI : ∫ r in (0:ℝ)..(0 + s), g r = ∫ r in (0:ℝ)..s, W r ω := by
          rw [zero_add]
          refine intervalIntegral.integral_congr (fun r hr => ?_)
          rw [Set.uIcc_of_le hs0.le] at hr
          simp [hg, max_eq_left hr.1]
        rw [eI] at hRs
        refine hRs.congr (fun n => Finset.sum_congr rfl (fun k _ => ?_))
        have h0 : (0:ℝ) ≤ 0 + k * s / n := by positivity
        simp only [hg]; rw [max_eq_left h0]
      have hlim := hY.sub (hRs'.const_mul lam)
      have eR : Y W A (0 + s) ω - Y W A 0 ω - lam * ∫ r in (0:ℝ)..s, W r ω = R W A lam s ω := by
        simp only [R, V, zero_add]
        have hY0 : Y W A 0 ω = 0 := by simp [Y, hP.zero ω]
        rw [hY0]; field_simp; ring
      rw [eR] at hlim
      exact hlim.limUnder_eq.symm
    · subst hs0
      refine ⟨fun _ => 0, stronglyMeasurable_const, Eventually.of_forall (fun ω => ?_)⟩
      exact hR0 ω
  have hR𝒢 : Rhist (R W A lam) t ≤ aeSigma P (Fhist A W t) := by
    refine iSup₂_le (fun s hs => ?_)
    intro G hG
    obtain ⟨E, hE, rfl⟩ := hG
    have hae := hmod s hs
    refine ⟨hae.mk _ ⁻¹' E, hae.stronglyMeasurable_mk.measurable hE, ?_⟩
    filter_upwards [hae.ae_eq_mk] with ω hω
    change (R W A lam s ω ∈ E) = (hae.mk _ ω ∈ E)
    rw [hω]
  have hRle : Rhist (R W A lam) t ≤ ‹MeasurableSpace Ω› :=
    iSup₂_le (fun s hs => (hRm s hs.1).comap_le)
  have hres := ae_eq_condExp_of_forall_setIntegral_eq hRle hDint (g := fun _ => (0:ℝ))
    (fun s _ _ => integrableOn_zero)
    (fun G hG _ => by
      obtain ⟨G', hG'm, hGG'⟩ := (measurableSet_aeSigma P _ G).1 (hR𝒢 G hG)
      rw [integral_zero, setIntegral_congr_set hGG', hkey G' hG'm])
    stronglyMeasurable_const.aestronglyMeasurable
  exact hres.symm
