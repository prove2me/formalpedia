-- Prove2me | solution 1 for TailRiskSharing.RobustVaR.theorem6_robust_var_comonotonic
-- status  : ACCEPTED   (disprove)
-- author  : @SamenHossain
-- created : 2026-10-11T16:18:51.958386+00:00
-- url     : https://prove2.me/submissions/15771a44-4eee-44d4-89ca-b1720b0b82d4

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

set_option autoImplicit false

open MeasureTheory TailRiskSharing.RobustVaR

-- Part A: an atomless probability space
namespace RVDisproof

open Set

/-- Atomlessness transfers along a measurable equivalence. -/
theorem A_atomless_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (hμ : TailRiskSharing.VaRConv.IsAtomless μ) :
    TailRiskSharing.VaRConv.IsAtomless (μ.map e) := by
  intro s hs hpos
  rw [e.map_apply] at hpos
  obtain ⟨t, hts, htm, htpos, htlt⟩ := hμ (e ⁻¹' s) (e.measurable hs) hpos
  refine ⟨e '' t, ?_, e.measurableSet_image.2 htm, ?_, ?_⟩
  · exact Set.image_subset_iff.2 hts
  · rw [e.map_apply, e.preimage_image]; exact htpos
  · rw [e.map_apply, e.map_apply, e.preimage_image]; exact htlt

/-- The cumulative function `c ↦ μ (s ∩ Iic c)` (as a real) for `μ = volume.restrict (Icc 0 1)`
is `1`-Lipschitz. -/
theorem A_lipschitz (s : Set ℝ) :
    LipschitzWith 1 (fun c : ℝ => ((volume.restrict (Icc (0:ℝ) 1)) (s ∩ Iic c)).toReal) := by
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμdef
  apply LipschitzWith.of_le_add
  intro x y
  have hfin : ∀ u : Set ℝ, μ u ≠ ⊤ := fun u => measure_ne_top μ u
  rcases le_total x y with hxy | hyx
  · have h1 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) :=
      measure_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.2 hxy))
    have h2 : (μ (s ∩ Iic x)).toReal ≤ (μ (s ∩ Iic y)).toReal :=
      ENNReal.toReal_mono (hfin _) h1
    have : 0 ≤ dist x y := dist_nonneg
    linarith
  · have hsub : s ∩ Iic x ⊆ (s ∩ Iic y) ∪ Ioc y x := by
      intro z hz
      by_cases hzy : z ≤ y
      · exact Or.inl ⟨hz.1, hzy⟩
      · exact Or.inr ⟨lt_of_not_ge hzy, hz.2⟩
    have h1 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) + μ (Ioc y x) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h3 : μ (Ioc y x) ≤ ENNReal.ofReal (x - y) := by
      calc μ (Ioc y x) ≤ volume (Ioc y x) := Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal (x - y) := Real.volume_Ioc
    have h4 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) + ENNReal.ofReal (x - y) :=
      h1.trans (add_le_add le_rfl h3)
    have h5 : (μ (s ∩ Iic x)).toReal ≤ (μ (s ∩ Iic y) + ENNReal.ofReal (x - y)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, ENNReal.ofReal_ne_top⟩) h4
    rw [ENNReal.toReal_add (hfin _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (sub_nonneg.2 hyx)] at h5
    have : dist x y = x - y := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx)]
    linarith

/-- `volume.restrict (Icc 0 1)` is atomless in the classical sense. -/
theorem A_atomless_real :
    TailRiskSharing.VaRConv.IsAtomless (volume.restrict (Icc (0:ℝ) 1)) := by
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμdef
  intro s hs hpos
  have hfin : ∀ u : Set ℝ, μ u ≠ ⊤ := fun u => measure_ne_top μ u
  set g : ℝ → ℝ := fun c => (μ (s ∩ Iic c)).toReal with hg
  have hcont : Continuous g := (A_lipschitz s).continuous
  have hg0 : g 0 = 0 := by
    have : μ (s ∩ Iic 0) = 0 := by
      rw [hμdef, Measure.restrict_apply (hs.inter measurableSet_Iic)]
      apply measure_mono_null (t := {0})
      · intro z hz
        simp only [mem_inter_iff, mem_Iic, mem_Icc] at hz
        simp only [mem_singleton_iff]
        linarith [hz.1.2, hz.2.1]
      · exact Real.volume_singleton
    simp [hg, this]
  have hg1 : g 1 = (μ s).toReal := by
    have : μ (s ∩ Iic 1) = μ s := by
      rw [hμdef, Measure.restrict_apply (hs.inter measurableSet_Iic), Measure.restrict_apply hs]
      congr 1
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.2⟩, h3⟩
    simp [hg, this]
  have hspos : 0 < (μ s).toReal := ENNReal.toReal_pos (ne_of_gt hpos) (hfin s)
  have hmem : (μ s).toReal / 2 ∈ Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    constructor <;> linarith
  obtain ⟨c, _, hc⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn hmem
  refine ⟨s ∩ Iic c, Set.inter_subset_left, hs.inter measurableSet_Iic, ?_, ?_⟩
  · have : 0 < (μ (s ∩ Iic c)).toReal := by
      have : g c = (μ (s ∩ Iic c)).toReal := rfl
      rw [← this, hc]; linarith
    exact ENNReal.toReal_pos_iff.1 this |>.1
  · rw [← ENNReal.toReal_lt_toReal (hfin _) (hfin _)]
    have : g c = (μ (s ∩ Iic c)).toReal := rfl
    rw [← this, hc]; linarith

universe u

theorem A_space : ∃ P : Measure (ULift.{u} ℝ), IsProbabilityMeasure P ∧
    TailRiskSharing.VaRConv.IsAtomless P ∧ ∃ A : Set (ULift.{u} ℝ), MeasurableSet A ∧ P A = 1 / 2 := by
  set e : ℝ ≃ᵐ ULift.{u} ℝ := MeasurableEquiv.ulift.symm with he
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμdef
  have hμprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμdef, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  refine ⟨μ.map e, ?_, A_atomless_map e μ A_atomless_real, ULift.down ⁻¹' Iic (1/2), ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  · exact measurable_down measurableSet_Iic
  · rw [e.map_apply]
    have hpre : e ⁻¹' (ULift.down ⁻¹' Iic (1/2 : ℝ)) = Iic (1/2 : ℝ) := by
      ext z; rfl
    rw [hpre, hμdef, Measure.restrict_apply measurableSet_Iic]
    have hset : Iic (1/2 : ℝ) ∩ Icc 0 1 = Icc 0 (1/2) := by
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [hset, Real.volume_Icc, sub_zero, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp

end RVDisproof

-- Part B: the robust VaR bound
namespace RVDisproof

open TailRiskSharing.VaRConv TailRiskSharing.TailConv

section B_helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The distribution function equals `1` above an a.e. bound. -/
lemma B_distFn_eq_one (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (x : ℝ) (hx : C ≤ x) : distFn P W x = 1 := by
  have h : ∀ᵐ ω ∂P, W ω ≤ x := hC.mono fun ω hω => ((le_abs_self _).trans hω).trans hx
  have h2 : {ω | W ω ≤ x} =ᵐ[P] (Set.univ : Set Ω) := by
    rw [ae_eq_univ]; exact ae_iff.mp h
  unfold distFn
  rw [measureReal_def, measure_congr h2, measure_univ, ENNReal.toReal_one]

/-- The distribution function vanishes below minus an a.e. bound. -/
lemma B_distFn_eq_zero (P : Measure Ω) (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (x : ℝ) (hx : x < -C) : distFn P W x = 0 := by
  have h0 : P {ω | ¬ |W ω| ≤ C} = 0 := ae_iff.mp hC
  have hsub : {ω | W ω ≤ x} ⊆ {ω | ¬ |W ω| ≤ C} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro h
    have := neg_abs_le (W ω)
    linarith
  unfold distFn
  rw [measureReal_def, measure_mono_null hsub h0, ENNReal.toReal_zero]

/-- The quantile `u ↦ VaRL P (1 - u) W` as an infimum. -/
lemma B_VaRL_one_sub (P : Measure Ω) (W : Ω → ℝ) (u : ℝ) :
    VaRL P (1 - u) W = sInf {x | u ≤ distFn P W x} := by
  unfold VaRL; rw [sub_sub_cancel]

/-- For `u ∈ (0,1]` the quantile set is bounded below by `-C` and contains `C`. -/
lemma B_qset (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    C ∈ {x | u ≤ distFn P W x} ∧ ∀ x ∈ {x | u ≤ distFn P W x}, -C ≤ x := by
  refine ⟨?_, ?_⟩
  · show u ≤ distFn P W C
    rw [B_distFn_eq_one P W C hC C le_rfl]; exact hu1
  · intro x hx
    by_contra h
    replace h := lt_of_not_ge h
    have := B_distFn_eq_zero P W C hC x h
    simp only [Set.mem_ofPred_eq] at hx
    linarith

lemma B_q_le (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    VaRL P (1 - u) W ≤ C := by
  obtain ⟨hmem, hlb⟩ := B_qset P W C hC u hu0 hu1
  rw [B_VaRL_one_sub]
  exact csInf_le ⟨-C, hlb⟩ hmem

lemma B_q_ge (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    -C ≤ VaRL P (1 - u) W := by
  obtain ⟨hmem, hlb⟩ := B_qset P W C hC u hu0 hu1
  rw [B_VaRL_one_sub]
  exact le_csInf ⟨C, hmem⟩ hlb

/-- The quantile is monotone on `(0,1]`. -/
lemma B_q_mono (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |W ω| ≤ C) (u v : ℝ) (hu0 : 0 < u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    VaRL P (1 - u) W ≤ VaRL P (1 - v) W := by
  obtain ⟨_, hlbu⟩ := B_qset P W C hC u hu0 (huv.trans hv1)
  obtain ⟨hmemv, _⟩ := B_qset P W C hC v (hu0.trans_le huv) hv1
  rw [B_VaRL_one_sub, B_VaRL_one_sub]
  refine csInf_le_csInf ⟨-C, hlbu⟩ ⟨C, hmemv⟩ ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  linarith

/-- The quantile of an `L^∞` variable is interval integrable on `[0,1]`. -/
lemma B_q_intervalIntegrable (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (hW : W ∈ Linf P) :
    IntervalIntegrable (fun u => VaRL P (1 - u) W) volume 0 1 := by
  obtain ⟨_, C, hC⟩ := hW
  let g : ℝ → ℝ := fun u => if u ≤ 0 then -C else VaRL P (1 - u) W
  have hg : MonotoneOn g (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    intro a ha b hb hab
    simp only [g]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact B_q_ge P W C hC b (lt_of_not_ge h2) hb.2
    · exfalso; exact h1 (hab.trans h2)
    · exact B_q_mono P W C hC a b (lt_of_not_ge h1) hab hb.2
  have hgi : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable
  refine hgi.congr ?_
  rw [Set.uIoc_of_le zero_le_one]
  intro u hu
  simp only [g, if_neg (not_le.mpr hu.1)]

/-- `W_1` as an interval integral. -/
lemma B_wassersteinK_one (P : Measure Ω) (Y Z : Ω → ℝ) :
    wassersteinK P 1 Y Z = ∫ x in (0:ℝ)..1, |VaRL P (1 - x) Y - VaRL P (1 - x) Z| := by
  unfold wassersteinK
  simp only [Real.rpow_one, div_one]

lemma B_wassersteinK_self (P : Measure Ω) (Z : Ω → ℝ) : wassersteinK P 1 Z Z = 0 := by
  rw [B_wassersteinK_one]
  simp

/-- The key estimate: every `Y` in the `W_1`-ball of radius `1` around `Z` has
`VaR^L_{3/4}(Y) ≤ 4 - K`. -/
lemma B_key (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Z ∈ Linf P) (K : ℝ)
    (hK : (1 / 2 : ℝ) ≤ P.real {ω | Z ω ≤ -K}) (Y : Ω → ℝ) (hY : Y ∈ Linf P)
    (hW : wassersteinK P 1 Y Z ≤ 1) : VaRL P (3 / 4) Y ≤ 4 - K := by
  obtain ⟨_, CY, hCY⟩ := hY
  obtain ⟨_, CZ, hCZ⟩ := hZ
  set t := VaRL P (3 / 4) Y with ht
  have ht' : t = VaRL P (1 - 1 / 4) Y := by rw [ht]; norm_num
  -- (iii)
  have hiii : ∀ u ∈ Set.Icc (1 / 4 : ℝ) 1, t ≤ VaRL P (1 - u) Y := by
    intro u hu
    rw [ht']
    exact B_q_mono P Y CY hCY (1 / 4) u (by norm_num) hu.1 hu.2
  -- (iv)
  have hiv : ∀ u : ℝ, 0 < u → u ≤ 1 / 2 → VaRL P (1 - u) Z ≤ -K := by
    intro u hu0 hu1
    obtain ⟨_, hlb⟩ := B_qset P Z CZ hCZ u hu0 (by linarith)
    rw [B_VaRL_one_sub]
    refine csInf_le ⟨-CZ, hlb⟩ ?_
    show u ≤ distFn P Z (-K)
    unfold distFn
    linarith
  -- (ii)
  have hint : IntervalIntegrable (fun u => |VaRL P (1 - u) Y - VaRL P (1 - u) Z|) volume 0 1 :=
    ((B_q_intervalIntegrable P Y ⟨‹_›, CY, hCY⟩).sub
      (B_q_intervalIntegrable P Z ⟨‹_›, CZ, hCZ⟩)).abs
  -- (v)
  have hsub : Set.uIcc (1 / 4 : ℝ) (1 / 2) ⊆ Set.uIcc 0 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hmain : (t + K) * (1 / 4) ≤ wassersteinK P 1 Y Z := by
    calc (t + K) * (1 / 4) = ∫ _ in (1 / 4 : ℝ)..(1 / 2), (t + K) := by
          rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
      _ ≤ ∫ u in (1 / 4 : ℝ)..(1 / 2), |VaRL P (1 - u) Y - VaRL P (1 - u) Z| := by
          refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
            (hint.mono_set hsub) ?_
          intro u hu
          have h1 := hiii u ⟨hu.1, by linarith [hu.2]⟩
          have h2 := hiv u (by linarith [hu.1]) hu.2
          exact le_trans (by linarith) (le_abs_self _)
      _ ≤ ∫ u in (0 : ℝ)..1, |VaRL P (1 - u) Y - VaRL P (1 - u) Z| := by
          refine intervalIntegral.integral_mono_interval (by norm_num) (by norm_num)
            (by norm_num) ?_ hint
          exact Filter.Eventually.of_forall fun u => abs_nonneg _
      _ = wassersteinK P 1 Y Z := (B_wassersteinK_one P Y Z).symm
  linarith

end B_helpers

theorem B_robust_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Z ∈ TailRiskSharing.TailConv.Linf P) (K : ℝ)
    (hK : (1 / 2 : ℝ) ≤ P.real {ω | Z ω ≤ -K}) :
    robust P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4)) Z ≤ 4 - K := by
  unfold robust
  apply csSup_le
  · exact ⟨_, Z, hZ, by rw [B_wassersteinK_self]; norm_num, rfl⟩
  · rintro r ⟨Y, hY, hW, rfl⟩
    exact B_key P Z hZ K hK Y hY hW

end RVDisproof

-- Part C: assembly
namespace RVDisproof

universe u


theorem C_const_mem_Linf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ) :
    (fun _ : Ω => c) ∈ TailRiskSharing.TailConv.Linf P :=
  ⟨measurable_const, |c|, Filter.Eventually.of_forall fun _ => le_rfl⟩

theorem C_ite_mem_Linf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (fun ω => if ω ∈ A then (-4 : ℝ) else 4) ∈ TailRiskSharing.TailConv.Linf P := by
  refine ⟨Measurable.ite hA measurable_const measurable_const, 4,
    Filter.Eventually.of_forall fun ω => ?_⟩
  dsimp only; split_ifs <;> norm_num

theorem C_neg_mem_Linf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Z ∈ TailRiskSharing.TailConv.Linf P) : -Z ∈ TailRiskSharing.TailConv.Linf P := by
  obtain ⟨hm, C, hC⟩ := hZ
  refine ⟨hm.neg, C, ?_⟩
  filter_upwards [hC] with ω hω
  simpa [abs_neg] using hω

theorem C_wasserstein_self_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) :
    wassersteinK P 1 Y Y = 0 := by
  unfold wassersteinK
  simp

theorem C_VaRL_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    TailRiskSharing.VaRConv.VaRL P (3 / 4) (fun _ : Ω => (0:ℝ)) = 0 := by
  unfold TailRiskSharing.VaRConv.VaRL
  have hset : {x : ℝ | 1 - 3 / 4 ≤ TailRiskSharing.VaRConv.distFn P (fun _ : Ω => (0:ℝ)) x}
      = Set.Ici 0 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, TailRiskSharing.VaRConv.distFn]
    by_cases hx : (0:ℝ) ≤ x
    · simp only [hx, Set.ofPred_true, probReal_univ]
      norm_num
    · simp only [hx, Set.ofPred_false, measureReal_empty]
      norm_num
  rw [hset, csInf_Ici]

theorem C_robust_zero_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    0 ≤ robust P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4)) (fun _ : Ω => (0:ℝ)) := by
  unfold robust
  by_cases hb : BddAbove (robustSet P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4))
      (fun _ : Ω => (0:ℝ)))
  · have hmem : (0:ℝ) ∈ robustSet P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4))
        (fun _ : Ω => (0:ℝ)) :=
      ⟨fun _ => 0, C_const_mem_Linf P 0, by rw [C_wasserstein_self_zero]; norm_num,
        (C_VaRL_zero P).symm⟩
    exact le_csSup hb hmem
  · rw [Real.sSup_of_not_bddAbove hb]


theorem C_real_Z {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    [DecidablePred (· ∈ A)] (hPA : P A = 1 / 2) :
    P.real {ω | (fun ω => if ω ∈ A then (-4 : ℝ) else 4) ω ≤ -4} = 1 / 2 := by
  have hset : {ω | (fun ω => if ω ∈ A then (-4 : ℝ) else 4) ω ≤ -4} = A := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hset, measureReal_def, hPA]
  simp

theorem C_real_negZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (hPA : P A = 1 / 2) :
    P.real {ω | (-(fun ω => if ω ∈ A then (-4 : ℝ) else 4)) ω ≤ -4} = 1 / 2 := by
  have hset : {ω | (-(fun ω => if ω ∈ A then (-4 : ℝ) else 4)) ω ≤ -4} = Aᶜ := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hset, probReal_compl_eq_one_sub hA, measureReal_def, hPA]
  norm_num


theorem C_mem_comonoAllocations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Z ∈ TailRiskSharing.TailConv.Linf P) :
    (fun i : Fin 2 => if i = 0 then Z else -Z) ∈
      TailRiskSharing.ComonoConv.ComonoAllocations P (TailRiskSharing.TailConv.Linf P) 2
        (fun _ : Ω => (0:ℝ)) := by
  refine ⟨⟨fun i => ?_, fun ω => ?_⟩, fun i => ?_⟩
  · by_cases hi : i = 0
    · simp only [hi, if_true]; exact hZ
    · simp only [hi, if_false]; exact C_neg_mem_Linf P Z hZ
  · simp [Fin.sum_univ_two]
  · exact ⟨Set.univ, MeasurableSet.univ, measure_univ, fun ω _ ω' _ => by simp⟩

theorem C_comonoInfConv_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ρ : Fin 2 → (Ω → ℝ) → ℝ) (Z : Ω → ℝ)
    (hZ : Z ∈ TailRiskSharing.TailConv.Linf P) :
    TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) ρ
        (fun _ : Ω => (0:ℝ)) ≤ ((ρ 0 Z + ρ 1 (-Z) : ℝ) : EReal) := by
  unfold TailRiskSharing.ComonoConv.comonoInfConv
  refine (iInf₂_le (fun i : Fin 2 => if i = 0 then Z else -Z)
    (C_mem_comonoAllocations P Z hZ)).trans_eq ?_
  simp [Fin.sum_univ_two]

end RVDisproof

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P) (Λ : TailRiskSharing.VaRConv.Side) (m : ℕ),
    (∀ (δs : Fin (m + 1) → ℝ) (α : ℝ), 0 < δs 0 → Monotone δs → 0 < α → α < 1 →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X =
          ((robust P 1 (δs 0) (TailRiskSharing.VaRConv.VaRS P Λ α) X + ∑ i : Fin m, δs i.succ / α : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 (δs i) (TailRiskSharing.VaRConv.VaRS P Λ α)) X
          (fun i => if i = 0 then X else 0)) ∧
    (∀ (αs : Fin (m + 1) → ℝ) (δ : ℝ), Antitone αs → αs 0 < 1 → 0 < αs (Fin.last m) → 0 < δ →
      TailRiskSharing.ComonoConv.comonoInfConv P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X =
          ((robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs 0)) X + ∑ i : Fin m, δ / αs i.succ : ℝ) : EReal) ∧
        IsOptimalComonoAllocation P (TailRiskSharing.TailConv.Linf P) (fun i => robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ (αs i))) X
          (fun i => if i = 0 then X else 0))) := by
  intro h
  obtain ⟨P, hprob, hatom, A, hA, hPA⟩ := RVDisproof.A_space.{0}
  classical
  obtain ⟨hE, -⟩ := (h (P := P) hatom (fun _ => 0) (RVDisproof.C_const_mem_Linf P 0)
    TailRiskSharing.VaRConv.Side.L 1).1 (fun _ => 1) (3 / 4) one_pos monotone_const
    (by norm_num) (by norm_num)
  have hS : TailRiskSharing.VaRConv.VaRS P TailRiskSharing.VaRConv.Side.L (3 / 4)
      = TailRiskSharing.VaRConv.VaRL P (3 / 4) := rfl
  set Z : ULift ℝ → ℝ := fun ω => if ω ∈ A then (-4 : ℝ) else 4 with hZdef
  have hZ : Z ∈ TailRiskSharing.TailConv.Linf P := RVDisproof.C_ite_mem_Linf P A hA
  have h1 : robust P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4)) Z ≤ 0 := by
    have := RVDisproof.B_robust_le P Z hZ 4 (by rw [RVDisproof.C_real_Z P A hPA])
    linarith
  have h2 : robust P 1 1 (TailRiskSharing.VaRConv.VaRL P (3 / 4)) (-Z) ≤ 0 := by
    have := RVDisproof.B_robust_le P (-Z) (RVDisproof.C_neg_mem_Linf P Z hZ) 4
      (by rw [RVDisproof.C_real_negZ P A hA hPA])
    linarith
  have h0 := RVDisproof.C_robust_zero_nonneg P
  have hle := RVDisproof.C_comonoInfConv_le P
    (fun i => robust P 1 ((fun _ : Fin (1 + 1) => (1:ℝ)) i)
      (TailRiskSharing.VaRConv.VaRS P TailRiskSharing.VaRConv.Side.L (3 / 4))) Z hZ
  rw [hE] at hle
  simp only [hS] at hle
  rw [EReal.coe_le_coe_iff] at hle
  have hsum : (∑ i : Fin 1, (fun _ : Fin (1 + 1) => (1:ℝ)) i.succ / (3 / 4)) = 4 / 3 := by
    norm_num
  rw [hsum] at hle
  linarith
