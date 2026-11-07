-- Prove2me | solution 1 for WolffPASTA.Main.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:23:37.394463+00:00
-- url     : https://prove2.me/submissions/7ebd2e0b-26e3-4e1c-8234-4d6fabbe0778

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting
import Theorems.Thm_WolffPASTA_Main_lemma_1
import Theorems.Thm_DurrettProbability_kronecker_lemma
import Theorems.Thm_LevyStochCalc_Probability_integral_sq_sum_of_condExp_eq_zero_readable

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


lemma sum_inv_sq_le_two (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i:ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have hb : ∀ i : ℕ, (((i:ℝ) + 1) ^ 2)⁻¹ ≤ 2 * (((i:ℝ) + 1)⁻¹ - (((i + 1 : ℕ) : ℝ) + 1)⁻¹) := by
    intro i
    push_cast
    have h1 : (0:ℝ) < (i:ℝ) + 1 := by positivity
    have h2 : (0:ℝ) < (i:ℝ) + 1 + 1 := by positivity
    have key : ((i:ℝ) + 1)⁻¹ - ((i:ℝ) + 1 + 1)⁻¹ = (((i:ℝ) + 1) * ((i:ℝ) + 1 + 1))⁻¹ := by
      field_simp; ring
    rw [key, show 2 * (((i:ℝ) + 1) * ((i:ℝ) + 1 + 1))⁻¹ = 2 / (((i:ℝ) + 1) * ((i:ℝ) + 1 + 1)) by ring,
      inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ i ∈ Finset.range n, (((i:ℝ) + 1) ^ 2)⁻¹
      ≤ ∑ i ∈ Finset.range n, 2 * (((i:ℝ) + 1)⁻¹ - (((i + 1 : ℕ) : ℝ) + 1)⁻¹) :=
        Finset.sum_le_sum (fun i _ => hb i)
    _ = 2 * (1 - ((n:ℝ) + 1)⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i : ℕ => ((i:ℝ) + 1)⁻¹)]
        simp
    _ ≤ 2 := by
        have : (0:ℝ) ≤ ((n:ℝ) + 1)⁻¹ := by positivity
        linarith

/-- Strong law for square-integrable martingale differences with bounded second moments
(Feller 1971, VII.8, Theorem 3, with `b_n = n`). -/
lemma l2_mds_slln {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : ∀ n, G n ≤ m0) (hmono : Monotone G)
    (D : ℕ → Ω → ℝ) (hL2 : ∀ n, MemLp (D n) 2 P)
    (hDm : ∀ n, StronglyMeasurable[G (n + 1)] (D n))
    (hD0 : ∀ n, P[D n | G n] =ᵐ[P] 0) (C : ℝ) (hC : ∀ n, ∫ ω, D n ω ^ 2 ∂P ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, D i ω) / n) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := le_trans (integral_nonneg (fun ω => sq_nonneg (D 0 ω))) (hC 0)
  set Y : ℕ → Ω → ℝ := fun k ω => ((k:ℝ) + 1)⁻¹ * D k ω with hYdef
  have hY : ∀ k, MemLp (Y k) 2 P := fun k => (hL2 k).const_mul _
  have hYm : ∀ k, StronglyMeasurable[G (k + 1)] (Y k) := fun k => (hDm k).const_mul _
  have hYc : ∀ k, P[Y k | G k] =ᵐ[P] 0 := by
    intro k
    have h := condExp_smul (μ := P) (((k:ℝ) + 1)⁻¹) (D k) (G k)
    have e : (((k:ℝ) + 1)⁻¹ • D k) = Y k := by funext ω; simp [hYdef, smul_eq_mul]
    rw [e] at h
    refine h.trans ?_
    filter_upwards [hD0 k] with ω hω
    simp [hω]
  have hsq := fun n => LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_readable
    (P := P) G hG hmono Y hY hYm hYc n
  set M : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, Y i ω with hMdef
  have hML2 : ∀ n, MemLp (M n) 2 P := fun n => memLp_finset_sum _ (fun i _ => hY i)
  have hMsq : ∀ n, ∫ ω, M n ω ^ 2 ∂P ≤ 2 * C := by
    intro n
    rw [hsq n]
    calc ∑ i ∈ Finset.range n, ∫ ω, Y i ω ^ 2 ∂P
        = ∑ i ∈ Finset.range n, (((i:ℝ) + 1) ^ 2)⁻¹ * ∫ ω, D i ω ^ 2 ∂P := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← integral_const_mul]
          congr 1; funext ω; simp only [hYdef]; rw [mul_pow, inv_pow]
      _ ≤ ∑ i ∈ Finset.range n, (((i:ℝ) + 1) ^ 2)⁻¹ * C :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC i) (by positivity))
      _ = (∑ i ∈ Finset.range n, (((i:ℝ) + 1) ^ 2)⁻¹) * C := by rw [Finset.sum_mul]
      _ ≤ 2 * C := mul_le_mul_of_nonneg_right (sum_inv_sq_le_two n) hC0
  let ℱ : Filtration ℕ m0 := ⟨G, hmono, hG⟩
  have hadp : StronglyAdapted ℱ M := by
    intro n
    exact Finset.stronglyMeasurable_fun_sum _ (fun i hi =>
      (hYm i).mono (hmono (by simp at hi; omega)))
  have hmart : Martingale M ℱ P := by
    refine martingale_of_condExp_sub_eq_zero_nat hadp (fun n => (hML2 n).integrable one_le_two)
      (fun n => ?_)
    have e : M (n + 1) - M n = Y n := by
      funext ω; simp [hMdef, Finset.sum_range_succ]
    rw [e]; exact hYc n
  have hbdd : ∀ n, eLpNorm (M n) 1 P ≤ ((1 + 2 * C) / 2).toNNReal := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hi : Integrable (fun ω => (1 + M n ω ^ 2) / 2) P :=
      ((integrable_const 1).add (hML2 n).integrable_sq).div_const 2
    calc ∫⁻ ω, ‖M n ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal ((1 + M n ω ^ 2) / 2) ∂P := by
          refine lintegral_mono (fun ω => ?_)
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|M n ω| - 1), sq_abs (M n ω)]
      _ = ENNReal.ofReal (∫ ω, (1 + M n ω ^ 2) / 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hi
            (Eventually.of_forall (fun ω => by
              show (0:ℝ) ≤ (1 + M n ω ^ 2) / 2; positivity))).symm
      _ ≤ ENNReal.ofReal ((1 + 2 * C) / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, integral_add (integrable_const 1) (hML2 n).integrable_sq]
          have := hMsq n
          norm_num [integral_const]
          linarith
      _ = (((1 + 2 * C) / 2).toNNReal : ENNReal) := rfl
  have hconv := hmart.submartingale.ae_tendsto_limitProcess hbdd
  filter_upwards [hconv] with ω hω
  have hk := DurrettProbability.kronecker_lemma (fun n => (n:ℝ) + 1) (fun n => D n ω)
    (fun n => by positivity) (fun a b hab => by simp only; linarith [(Nat.cast_le.mpr hab : (a:ℝ) ≤ b)])
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    ⟨_, hω.congr (fun n => by
      simp only [hMdef, hYdef]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [div_eq_inv_mul])⟩
  have h2 : Tendsto (fun n : ℕ => ((n:ℝ) + 1) / n) atTop (𝓝 1) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have := hk.mul h2
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp



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

end WolffPASTAAux

open WolffPASTAAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAAJoint P A (U N B))
    (h : ℝ) (hh : 0 < h) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => R (U N B) A lam (n * h) ω / n) atTop (𝓝 0) := by
  have hP : IsPoissonProcessWithIntensity P A (fun _ => lam) := hA
  have hU : ∀ s ω, 0 ≤ s → 0 ≤ U N B s ω ∧ U N B s ω ≤ 1 := by
    intro s ω _
    simp only [U, Set.indicator]
    split_ifs <;> norm_num
  obtain ⟨_, hmart⟩ := lemma_1 P N A lam hlam hA B hB hpath hjoint hLAA
  set W := U N B with hW
  have hRm : ∀ s, 0 ≤ s → Measurable (R W A lam s) :=
    fun s hs => R_measurable A hP.meas hP.mono W hjoint lam s hs
  set G : ℕ → MeasurableSpace Ω := fun n => Rhist (R W A lam) (n * h) with hGdef
  have hG : ∀ n, G n ≤ ‹MeasurableSpace Ω› := fun n =>
    iSup₂_le (fun s hs => (hRm s hs.1).comap_le)
  have hmono : Monotone G := by
    intro n m hnm
    refine biSup_mono (fun s hs => ⟨hs.1, le_trans hs.2 ?_⟩)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) hh.le
  have hcomap : ∀ t s, s ∈ Set.Icc (0:ℝ) t → Measurable[Rhist (R W A lam) t] (R W A lam s) :=
    fun t s hs => (comap_measurable _).mono
      (le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0:ℝ) t) =>
        MeasurableSpace.comap (R W A lam s) inferInstance) s hs) le_rfl
  set D : ℕ → Ω → ℝ := fun n ω => R W A lam (n * h + h) ω - R W A lam (n * h) ω with hDdef
  have hnh : ∀ n : ℕ, (0:ℝ) ≤ n * h := fun n => by positivity
  have hDm : ∀ n, StronglyMeasurable[G (n + 1)] (D n) := by
    intro n
    have hle : (n:ℝ) * h + h ≤ ((n + 1 : ℕ) : ℝ) * h := by push_cast; linarith
    exact ((hcomap _ _ ⟨by linarith [hnh n], hle⟩).sub
      (hcomap _ _ ⟨hnh n, by linarith⟩)).stronglyMeasurable
  have hD0 : ∀ n, P[D n | G n] =ᵐ[P] 0 := fun n => hmart (n * h) h (hnh n) hh
  -- increments of A
  set dA : ℕ → Ω → ℕ := fun n ω => A (n * h + h) ω - A (n * h) ω with hdA
  have hdAm : ∀ n, Measurable (dA n) := fun n => (hP.meas _).sub (hP.meas _)
  have hlaw : ∀ n, P.map (dA n) = poissonMeasure (lam * h).toNNReal := by
    intro n
    have := hP.law (n * h) (n * h + h) (hnh n) (by linarith)
    rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, mul_comm h lam] at this
    exact this
  have hgsq : Measurable (fun n : ℕ => (n : ℝ) ^ 2) := measurable_from_nat
  have hint2 : ∀ n, Integrable (fun ω => (dA n ω : ℝ) ^ 2) P := by
    intro n
    have h1 := (pois_integral_sq (lam * h).toNNReal).1
    rw [← hlaw n] at h1
    exact (integrable_map_measure h1.aestronglyMeasurable (hdAm n).aemeasurable).mp h1
  have hval2 : ∀ n, ∫ ω, (dA n ω : ℝ) ^ 2 ∂P = lam * h + (lam * h) ^ 2 := by
    intro n
    have h1 := (pois_integral_sq (lam * h).toNNReal).2
    rw [← hlaw n, integral_map (hdAm n).aemeasurable hgsq.aestronglyMeasurable] at h1
    rw [h1, Real.coe_toNNReal _ (by positivity)]
  have hbd : ∀ n ω, D n ω ^ 2 ≤ (dA n ω : ℝ) ^ 2 + lam ^ 2 * h ^ 2 ∧
      |D n ω| ≤ (dA n ω : ℝ) + lam * h := by
    intro n ω
    have := R_incr_bound A hP.mono lam hlam W hU hjoint ω (n * h) (n * h + h) (hnh n)
      (by linarith)
    simp only [add_sub_cancel_left] at this
    exact this
  have hDmeas : ∀ n, Measurable (D n) := fun n =>
    (hRm _ (by linarith [hnh n])).sub (hRm _ (hnh n))
  have hL2 : ∀ n, MemLp (D n) 2 P := by
    intro n
    have hg2 : MemLp (fun ω => (dA n ω : ℝ) + lam * h) 2 P := by
      have : MemLp (fun ω => (dA n ω : ℝ)) 2 P :=
        (memLp_two_iff_integrable_sq
          (measurable_from_nat.comp (hdAm n)).aestronglyMeasurable).mpr (hint2 n)
      exact this.add (memLp_const _)
    refine hg2.of_le (hDmeas n).aestronglyMeasurable (Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ _ + lam * h)]
    exact (hbd n ω).2
  have hC : ∀ n, ∫ ω, D n ω ^ 2 ∂P ≤ lam * h + 2 * lam ^ 2 * h ^ 2 := by
    intro n
    calc ∫ ω, D n ω ^ 2 ∂P ≤ ∫ ω, ((dA n ω : ℝ) ^ 2 + lam ^ 2 * h ^ 2) ∂P :=
          integral_mono (hL2 n).integrable_sq ((hint2 n).add (integrable_const _))
            (fun ω => (hbd n ω).1)
      _ = lam * h + 2 * lam ^ 2 * h ^ 2 := by
          rw [integral_add (hint2 n) (integrable_const _), hval2]
          simp
          ring
  have hslln := l2_mds_slln P G hG hmono D hL2 hDm hD0 _ hC
  filter_upwards [hslln] with ω hω
  have hR0 : R W A lam 0 ω = 0 := by simp [R, Y, V, hP.zero ω]
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, D i ω = R W A lam (n * h) ω := by
    intro n
    induction n with
    | zero => simp [hR0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [hDdef]
      have : ((n + 1 : ℕ) : ℝ) * h = n * h + h := by push_cast; ring
      rw [this]; ring
  exact hω.congr (fun n => by rw [htel])
