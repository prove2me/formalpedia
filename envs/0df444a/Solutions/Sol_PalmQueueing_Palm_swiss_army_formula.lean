-- Prove2me | solution 1 for PalmQueueing.Palm.swiss_army_formula
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:31:50.704981+00:00
-- url     : https://prove2.me/submissions/76124099-b175-4606-afd2-9bab268e02f9

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_SwissArmySetting

/-!
# Theorem 1.3.1: the Swiss army formula of Palm calculus (§1.3.7, p.29)
-/


namespace PalmQueueing.Palm

open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

lemma count_apply (N : PointProcess Ω) (ω : Ω) (C : Set ℝ) (hC : MeasurableSet C) :
    N.count ω C = ∑' n : ℤ, C.indicator (fun _ => (1:ℝ≥0∞)) (N.T n ω) := by
  simp [PointProcess.count, Measure.sum_apply _ hC, Measure.dirac_apply' _ hC]
  rfl

lemma count_Ioc_lt_top (N : PointProcess Ω) (ω : Ω) (a b : ℝ) :
    N.count ω (Set.Ioc a b) < ⊤ := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((N.tendsto_atTop ω).eventually (eventually_gt_atTop b))
  obtain ⟨m, hm⟩ := eventually_atBot.1 ((N.tendsto_atBot ω).eventually (eventually_le_atBot a))
  rw [count_apply N ω _ measurableSet_Ioc]
  rw [tsum_eq_sum (s := Finset.Icc m M)]
  · exact ENNReal.sum_lt_top.2 (fun n _ => by
      rw [Set.indicator_apply]; split_ifs <;> simp)
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_Ioc, not_and, not_le]
    intro h1
    rcases hn with hn | hn
    · have := hm n hn.le; linarith
    · have := hM n hn.le; linarith

/-! ### A counterexample: the periodic process with `X ≡ 1` -/

noncomputable section

abbrev Circ := AddCircle (1:ℝ)

instance circFact : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

def clift (x : Circ) : ℝ := (AddCircle.equivIoc (1:ℝ) (-1) x : ℝ)

lemma clift_mem (x : Circ) : clift x ∈ Set.Ioc (-1:ℝ) 0 := by
  obtain ⟨h1, h2⟩ := (AddCircle.equivIoc (1:ℝ) (-1) x).2
  exact ⟨h1, by unfold clift; linarith⟩

lemma coe_clift (x : Circ) : ((clift x : ℝ) : Circ) = x := AddCircle.coe_equivIoc

lemma clift_coe {u : ℝ} (hu : u ∈ Set.Ioc (-1:ℝ) 0) : clift (u : Circ) = u := by
  unfold clift
  rw [AddCircle.equivIoc_coe_of_mem (by simpa using hu)]

lemma measurable_clift : Measurable clift :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1:ℝ) (-1)).measurable

def cflow : Flow Circ where
  toFun t x := ((-t : ℝ) : Circ) + x
  measurable_uncurry := by
    apply Continuous.measurable
    have h0 : Continuous fun p : ℝ × Circ => -p.1 :=
      (continuous_fst : Continuous fun p : ℝ × Circ => p.1).neg
    have h1 : Continuous fun p : ℝ × Circ => ((-p.1 : ℝ) : Circ) :=
      continuous_quot_mk.comp h0
    have h2 : Continuous fun p : ℝ × Circ => p.2 := continuous_snd
    exact h1.add h2
  measurable' t := by
    apply Continuous.measurable
    exact (continuous_const : Continuous fun _ : Circ => ((-t:ℝ):Circ)).add
      (continuous_id : Continuous fun x : Circ => x)
  map_zero := by ext x; simp
  map_add s t := by
    ext x
    simp only [Function.comp, neg_add, AddCircle.coe_add, add_assoc]

def cpp : PointProcess Circ where
  T n x := clift x + n
  measurable_T n := measurable_clift.add_const _
  strictMono x := fun a b hab => by
    simp only
    linarith [(Int.cast_lt.2 hab : (a:ℝ) < b)]
  zero_le x := by simp [(clift_mem x).2]
  lt_one x := by
    have := (clift_mem x).1
    simp only [Int.cast_one]
    linarith
  tendsto_atTop x := tendsto_atTop_add_const_left _ _ tendsto_intCast_atTop_atTop
  tendsto_atBot x := tendsto_atBot_add_const_left _ _ (tendsto_intCast_atBot_iff.2 tendsto_id)

lemma cpp_T (n : ℤ) (x : Circ) : cpp.T n x = clift x + n := rfl

lemma key_integral (t : ℝ) (ht : 0 < t) :
    ∫⁻ x, cpp.count x (Set.Ioc 0 t) ∂(volume : Measure Circ) = ENNReal.ofReal t := by
  simp_rw [count_apply cpp _ _ measurableSet_Ioc, cpp_T]
  rw [← AddCircle.lintegral_preimage (1:ℝ) (-1)]
  have h1 : ∫⁻ u in Set.Ioc (-1:ℝ) (-1 + 1), ∑' n : ℤ,
      (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (clift (u : Circ) + n)
      = ∫⁻ u in Set.Ioc (-1:ℝ) (-1 + 1), ∑' n : ℤ,
      (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (u + n) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [clift_coe (by simpa using hu)]
  rw [h1]
  rw [lintegral_tsum (f := fun (n : ℤ) (u : ℝ) =>
    (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (u + n)) (fun n => (show Measurable fun u : ℝ =>
    (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (u + n) from
    (measurable_const.indicator measurableSet_Ioc).comp (measurable_id.add_const _)).aemeasurable)]
  have h2 : ∀ n : ℤ, ∫⁻ u in Set.Ioc (-1:ℝ) (-1 + 1),
      (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (u + n)
      = volume (Set.Ioc 0 t ∩ Set.Ioc ((n:ℝ) - 1) n) := by
    intro n
    have e1 : (fun u : ℝ => (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (u + n))
        = ((fun u : ℝ => (n:ℝ) + u) ⁻¹' Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) := by
      classical
      ext u
      simp only [Set.indicator_apply, Set.mem_preimage, show (n:ℝ) + u = u + n from add_comm _ _]
    have hm : MeasurableSet ((fun u : ℝ => (n:ℝ) + u) ⁻¹' Set.Ioc 0 t) :=
      measurableSet_Ioc.preimage (measurable_const_add _)
    rw [e1, lintegral_indicator_const hm, one_mul, Measure.restrict_apply hm]
    have e2 : (fun u : ℝ => (n:ℝ) + u) ⁻¹' Set.Ioc 0 t ∩ Set.Ioc (-1) (-1 + 1)
        = (fun u : ℝ => (n:ℝ) + u) ⁻¹' (Set.Ioc 0 t ∩ Set.Ioc ((n:ℝ) - 1) n) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, b⟩, by linarith, by linarith⟩
      · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, b⟩, by linarith, by linarith⟩
    rw [e2, measure_preimage_add]
  simp_rw [h2]
  have hd : Pairwise (Function.onFun Disjoint fun n : ℤ => Set.Ioc 0 t ∩ Set.Ioc ((n:ℝ) - 1) n) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨_, hv1, hv2⟩ ⟨_, hw1, hw2⟩
    rcases lt_or_gt_of_ne hmn with h | h
    · have : (m:ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
    · have : (n:ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
  have hmeas : ∀ n : ℤ, MeasurableSet (Set.Ioc 0 t ∩ Set.Ioc ((n:ℝ) - 1) n) :=
    fun n => measurableSet_Ioc.inter measurableSet_Ioc
  have h3 : (⋃ n : ℤ, Set.Ioc 0 t ∩ Set.Ioc ((n:ℝ) - 1) n) = Set.Ioc 0 t := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨n, h, _⟩; exact h
    · intro h
      exact ⟨⌈v⌉, h, by linarith [Int.ceil_lt_add_one v], Int.le_ceil v⟩
  rw [← measure_iUnion hd hmeas, h3, Real.volume_Ioc, sub_zero]

lemma clift_shift (t : ℝ) (x : Circ) : ∃ k : ℤ, clift (cflow t x) = clift x - t + k := by
  have h : ((clift (cflow t x) : ℝ) : Circ) = ((clift x - t : ℝ) : Circ) := by
    rw [coe_clift, AddCircle.coe_sub, coe_clift]
    show ((-t:ℝ) : Circ) + x = x - (t : Circ)
    rw [AddCircle.coe_neg]; abel
  have h2 : ((clift (cflow t x) - (clift x - t) : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).1 h2
  refine ⟨k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  linarith

lemma cpp_compatible : cpp.Compatible cflow := by
  intro t x C hC
  rw [count_apply _ _ _ hC, count_apply _ _ _ (measurable_sub_const t hC)]
  simp_rw [cpp_T]
  obtain ⟨k, hk⟩ := clift_shift t x
  rw [hk]
  have e1 : ∀ n : ℤ, C.indicator (fun _ => (1:ℝ≥0∞)) (clift x - t + k + n)
      = C.indicator (fun _ => (1:ℝ≥0∞)) (clift x + ((k + n : ℤ) : ℝ) - t) := by
    intro n; congr 1; push_cast; ring
  simp_rw [e1]
  have e2 := (Equiv.addLeft k).tsum_eq
    (fun n : ℤ => C.indicator (fun _ => (1:ℝ≥0∞)) (clift x + (n:ℝ) - t))
  simp only [Equiv.coe_addLeft] at e2
  rw [e2]
  classical
  exact tsum_congr fun n => by simp only [Set.indicator_apply, Set.mem_preimage]

lemma cflow_T (n : ℤ) (x : Circ) : cflow (cpp.T n x) x = 0 := by
  show ((-(clift x + n) : ℝ) : Circ) + x = 0
  calc ((-(clift x + n) : ℝ) : Circ) + x
      = ((-(clift x + n) : ℝ) : Circ) + ((clift x : ℝ) : Circ) := by rw [coe_clift]
    _ = (((-(clift x + n) + clift x : ℝ)) : Circ) := (AddCircle.coe_add (1:ℝ) _ _).symm
    _ = ((-n : ℝ) : Circ) := by congr 1; ring
    _ = 0 := (AddCircle.coe_eq_zero_iff (1:ℝ)).2 ⟨-n, by simp⟩

lemma cpalm : IsPalmProbability cflow cpp volume (Measure.dirac 0) 1 := by
  refine ⟨inferInstance, ?_⟩
  intro A hA t ht
  simp_rw [cflow_T]
  rw [Measure.dirac_apply' _ hA]
  simp_rw [ENNReal.tsum_mul_right]
  have hm : Measurable fun x : Circ => ∑' n : ℤ, (Set.Ioc 0 t).indicator (fun _ => (1:ℝ≥0∞)) (cpp.T n x) :=
    Measurable.tsum fun n => (measurable_const.indicator measurableSet_Ioc).comp (cpp.measurable_T n)
  rw [lintegral_mul_const _ hm]
  simp_rw [← count_apply cpp _ _ measurableSet_Ioc]
  rw [key_integral t ht, one_mul]
  rfl

def cPS : PalmSetting Circ where
  θ := cflow
  N := cpp
  P := volume
  P0 := Measure.dirac 0
  lam := 1
  isProb := ⟨by simp [AddCircle.measure_univ]⟩
  invariant := fun t => map_add_left_eq_self volume _
  compatible := cpp_compatible
  intensity := ⟨one_pos, by rw [key_integral 1 one_pos]⟩
  palm := cpalm

lemma id_measure_eq : (StieltjesFunction.id).measure = (volume : Measure ℝ) := by
  refine Measure.ext_of_Ioc _ _ (fun a b hab => ?_)
  rw [StieltjesFunction.measure_Ioc, Real.volume_Ioc]
  rfl

def cB : Integrator Circ := ⟨fun _ => StieltjesFunction.id, fun _ => measurable_const⟩

lemma cD_count (D : InstantFamily Circ) (hD : D.tau = cpp.T) (ω : Circ) :
    D.count ω = cpp.count ω := by
  simp only [InstantFamily.count, PointProcess.count, hD]

def cSAS : SwissArmySetting Circ where
  toPalmSetting := cPS
  D := ⟨cpp.T, cpp.measurable_T⟩
  W := fun _ _ => 0
  X := fun _ _ => 1
  Xl := fun _ _ => 1
  B := cB
  Z := fun _ _ => 1
  D_locallyFinite := fun ω a b => by
    rw [cD_count _ rfl]
    refine lt_of_le_of_lt (measure_mono (show Set.Icc a b ⊆ Set.Ioc (a - 1) b from ?_))
      (count_Ioc_lt_top cpp ω (a - 1) b)
    intro v hv; exact ⟨by linarith [hv.1], hv.2⟩
  D_simple := fun ω x => by
    rw [cD_count _ rfl, count_apply _ _ _ (measurableSet_singleton x)]
    simp_rw [cpp_T]
    by_cases h : ∃ n0 : ℤ, clift ω + n0 = x
    · obtain ⟨n0, hn0⟩ := h
      rw [tsum_eq_single n0]
      · rw [Set.indicator_of_mem (by simpa using hn0)]
      · intro n hn
        rw [Set.indicator_of_notMem]
        simp only [Set.mem_singleton_iff]
        intro h'
        apply hn
        have : (n:ℝ) = n0 := by linarith
        exact_mod_cast this
    · push_neg at h
      have : ∀ n : ℤ, ({x} : Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) (clift ω + n) = 0 := by
        intro n
        rw [Set.indicator_of_notMem]
        simpa using h n
      simp [this]
  biInfinite := fun ω => by
    rw [cD_count _ rfl, count_apply _ _ _ measurableSet_Ici, count_apply _ _ _ measurableSet_Iio]
    simp_rw [cpp_T]
    have hl := clift_mem ω
    constructor
    · apply eq_top_iff.2
      have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
        intro a b hab; simpa using hab
      refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
      have : ∀ k : ℕ, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞))
          (clift ω + (((k : ℤ) + 1 : ℤ) : ℝ)) = 1 := by
        intro k
        rw [Set.indicator_of_mem]
        simp only [Set.mem_Ici]
        push_cast
        linarith [hl.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      simp_rw [this]
      rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    · apply eq_top_iff.2
      have hinj : Function.Injective (fun k : ℕ => -(k : ℤ) - 1) := by
        intro a b hab; simpa using hab
      refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
      have : ∀ k : ℕ, (Set.Iio (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞))
          (clift ω + ((-(k : ℤ) - 1 : ℤ) : ℝ)) = 1 := by
        intro k
        rw [Set.indicator_of_mem]
        simp only [Set.mem_Iio]
        push_cast
        linarith [hl.2, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      simp_rw [this]
      rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
  sojourn := fun n ω => ⟨sub_self _, le_rfl⟩
  markSequence := ⟨fun n => measurable_const, fun n k ω => rfl⟩
  X_nonneg_int := fun t ω => ⟨zero_le_one, 1, by simp⟩
  balance := fun a b ω _ => by
    rw [cD_count _ rfl]
    show (1:ℝ) - 1 = (cpp.count ω (Set.Ioc a b)).toReal - (cpp.count ω (Set.Ioc a b)).toReal
    simp
  leftLimit := fun s ω => tendsto_const_nhds
  Z_nonneg := fun _ _ => zero_le_one
  Z_measurable := fun _ => measurable_const
  X_measurable := fun _ => measurable_const
  Xl_measurable := fun _ => measurable_const
  Z_compatible := fun _ _ _ => rfl
  A_compatible := cpp_compatible
  D_compatible := fun t ω C hC => by
    rw [cD_count _ rfl, cD_count _ rfl]; exact cpp_compatible t ω C hC
  X_compatible := fun _ _ _ => rfl
  B_compatible := fun t ω C hC => by
    show StieltjesFunction.id.measure C = StieltjesFunction.id.measure ((fun s => s - t) ⁻¹' C)
    rw [id_measure_eq]
    have : (fun s : ℝ => s - t) ⁻¹' C = (fun s : ℝ => (-t) + s) ⁻¹' C := by
      ext s; simp [sub_eq_neg_add]
    rw [this, measure_preimage_add]

theorem swiss_army_false : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (S : SwissArmySetting Ω) (t : ℝ)
    (ht : 0 < t),
    ENNReal.ofReal S.toPalmSetting.lam *
        ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) (S.W 0 ω), ENNReal.ofReal (S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P0
      = (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (S.Xl s ω * S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P) / ENNReal.ofReal t) := by
  intro H
  have h := H cSAS 1 one_pos
  have hL : (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) (cSAS.W 0 ω), ENNReal.ofReal (cSAS.Z s ω)
      ∂((cSAS.B.B ω).measure) ∂cSAS.toPalmSetting.P0) = 0 := by
    show (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) 0, ENNReal.ofReal 1
      ∂(StieltjesFunction.id.measure) ∂(Measure.dirac (0 : Circ))) = 0
    simp
  have hR : (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (cSAS.Xl s ω * cSAS.Z s ω)
      ∂((cSAS.B.B ω).measure) ∂cSAS.toPalmSetting.P) = 1 := by
    show (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (1 * 1)
      ∂(StieltjesFunction.id.measure) ∂(volume : Measure Circ)) = 1
    rw [id_measure_eq]
    simp [AddCircle.measure_univ]
  rw [hL, hR] at h
  show False
  have : (ENNReal.ofReal cSAS.toPalmSetting.lam * 0 : ℝ≥0∞) = 0 := mul_zero _
  rw [this] at h
  simp at h

end

end PalmQueueing.Palm

open PalmQueueing.Palm
open MeasureTheory

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (S : SwissArmySetting Ω) (t : ℝ) (ht : 0 < t),
    ENNReal.ofReal S.toPalmSetting.lam *
        ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) (S.W 0 ω), ENNReal.ofReal (S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P0
      = (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (S.Xl s ω * S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P) / ENNReal.ofReal t) := by
  exact swiss_army_false
