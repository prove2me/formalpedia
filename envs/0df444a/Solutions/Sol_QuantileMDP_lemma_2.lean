-- Prove2me | solution 1 for QuantileMDP.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-13T16:47:57.27225+00:00
-- url     : https://prove2.me/submissions/cf93cd01-0652-4f9c-8da5-20a95769c735

import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_opt

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace QuantileMDP

/-- On a finite support, a strict lower tail can be represented by a closed lower
tail at a strictly smaller threshold. -/
private theorem exists_closed_cut (μ : Measure ℝ) {S : Set ℝ} (hS : S.Finite)
    (hsupport : μ Sᶜ = 0) (x : ℝ) :
    ∃ y < x, μ (Iic y) = μ (Iio x) := by
  have hfinite : (S ∩ Iio x).Finite := hS.subset inter_subset_left
  have hex : ∃ y < x, ∀ z ∈ S ∩ Iio x, z ≤ y := by
    by_cases h : (S ∩ Iio x).Nonempty
    · obtain ⟨y, hy, hymax⟩ := Set.exists_max_image (S ∩ Iio x) id hfinite h
      exact ⟨y, hy.2, hymax⟩
    · exact ⟨x - 1, by linarith, fun z hz => (h ⟨z, hz⟩).elim⟩
  obtain ⟨y, hy, hcover⟩ := hex
  refine ⟨y, hy, measure_eq_measure_of_null_sdiff (Iic_subset_Iio.mpr hy) ?_⟩
  apply measure_mono_null _ hsupport
  intro z hz hzS
  exact hz.2 (hcover z ⟨hzS, hz.1⟩)

private theorem measure_Ici_eq_one_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ (Ici x) = 1 ↔ μ (Iio x) = 0 := by
  have h := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := x))
  rw [compl_Iio] at h
  constructor
  · intro he
    rw [he] at h
    have hreal := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (measure_ne_top μ _) (by simp)] at hreal
    have heq : (μ (Iio x)).toReal = 0 := by linarith
    exact ((ENNReal.toReal_eq_zero_iff _).mp heq).resolve_right (measure_ne_top μ _)
  · intro he
    simpa [he] using h

private theorem quantile_ge_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] {S : Set ℝ}
    (hS : S.Finite) (hsupport : μ Sᶜ = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    (x : EReal) ≤ quantile μ t ↔
      (μ (Iio x)).toReal < t ∨ (μ (Iio x)).toReal = 0 := by
  obtain ⟨y, hy, hcut⟩ := exists_closed_cut μ hS hsupport x
  have hzero : (μ (Iio x)).toReal = 0 ↔ μ (Iio x) = 0 := by
    simp [ENNReal.toReal_eq_zero_iff, measure_ne_top]
  by_cases ht0 : t = 0
  · subst t
    rw [quantile, if_pos rfl, or_iff_right (not_lt.mpr ENNReal.toReal_nonneg), hzero]
    constructor
    · intro hx
      by_contra hn
      have hub : sSup ((fun z : ℝ => (z : EReal)) '' {D : ℝ | μ (Ici D) = 1}) ≤ (y : EReal) := by
        apply sSup_le
        rintro _ ⟨z, hz, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! hzy
        have : μ (Iic y) = 0 :=
          measure_mono_null (Iic_subset_Iio.mpr hzy) ((measure_Ici_eq_one_iff μ z).mp hz)
        exact hn (hcut ▸ this)
      exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr hy)) (hx.trans hub)
    · intro hx
      exact le_sSup ⟨x, (measure_Ici_eq_one_iff μ x).mpr hx, rfl⟩
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [or_iff_left_of_imp (fun hz => hz ▸ htpos)]
    have hlt : (μ (Iio x)).toReal < t ↔ μ (Iio x) < ENNReal.ofReal t :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ _)).symm
    rw [hlt]
    by_cases ht1 : t = 1
    · subst t
      rw [quantile, if_neg ht0, if_pos rfl, ENNReal.ofReal_one]
      constructor
      · intro hx
        by_contra! hn
        have hy1 : μ (Iic y) = 1 :=
          hcut.trans (le_antisymm prob_le_one hn)
        exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr hy))
          (hx.trans (sInf_le ⟨y, hy1, rfl⟩))
      · intro hx
        apply le_sInf
        rintro _ ⟨z, hz, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! hzx
        exact (not_le_of_gt hx) (hz ▸ measure_mono (Iic_subset_Iio.mpr hzx))
    · rw [quantile, if_neg ht0, if_neg ht1]
      constructor
      · intro hx
        by_contra! hn
        have hreach : ENNReal.ofReal t ≤ μ (Iic y) := hcut.symm ▸ hn
        exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr hy))
          (hx.trans (sInf_le ⟨y, hreach, rfl⟩))
      · intro hx
        apply le_sInf
        rintro _ ⟨z, hz, rfl⟩
        apply EReal.coe_le_coe_iff.mpr
        by_contra! hzx
        exact (not_le_of_gt hx) (hz.trans (measure_mono (Iic_subset_Iio.mpr hzx)))

/-- The quantile of a finitely supported probability is a real threshold. -/
private theorem quantile_eq_coe (μ : Measure ℝ) [IsProbabilityMeasure μ] {S : Set ℝ}
    (hS : S.Finite) (hsupport : μ Sᶜ = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x : ℝ, quantile μ t = (x : EReal) := by
  obtain ⟨a, ha⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  have ha0 : μ (Iio a) = 0 := by
    apply measure_mono_null _ hsupport
    intro y hy hyS
    exact (not_lt_of_ge (ha hyS)) hy
  have hb1 : μ (Iio (b + 1)) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_eq_measure_of_null_sdiff (subset_univ _)
    apply measure_mono_null _ hsupport
    intro y hy hyS
    exact hy.2 ((hb hyS).trans_lt (by linarith : b < b + 1))
  have hlo := (quantile_ge_iff μ hS hsupport ht a).mpr (Or.inr (by simp [ha0]))
  have hhi : ¬ ((b + 1 : ℝ) : EReal) ≤ quantile μ t := by
    rw [quantile_ge_iff μ hS hsupport ht, hb1]
    simpa using ht.2
  exact ⟨(quantile μ t).toReal,
    (EReal.coe_toReal (ne_of_lt (lt_of_lt_of_le (lt_of_not_ge hhi) le_top))
      (ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe a) hlo))).symm⟩

private theorem partition_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : ⋃ i, A i = univ) (B : Set Ω) (hB : MeasurableSet B) :
    P B = ∑ i, P (A i ∩ B) := by
  have hunion : (⋃ i, A i ∩ B) = B := by
    rw [← iUnion_inter, hcover, univ_inter]
  have hd : Pairwise (fun i j => Disjoint (A i ∩ B) (A j ∩ B)) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  calc
    P B = P (⋃ i, A i ∩ B) := congrArg P hunion.symm
    _ = ∑' i, P (A i ∩ B) := measure_iUnion hd (fun i => (hA i).inter hB)
    _ = ∑ i, P (A i ∩ B) := tsum_fintype _

/-- For any feasible allocation, its branchwise minimum is bounded by the
mixture quantile. Allocations equal to one can discard their branches. -/
private theorem branch_min_le {ι : Type*} [Fintype ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {S : Set ℝ} (hS : S.Finite) (hsupport : μ Sᶜ = 0)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (ν : ι → Measure ℝ)
    (hprob : ∀ i, 0 < p i → IsProbabilityMeasure (ν i))
    (T : ι → Set ℝ) (hT : ∀ i, (T i).Finite) (hν : ∀ i, ν i (T i)ᶜ = 0)
    (hmix : ∀ x : ℝ, (μ (Iio x)).toReal = ∑ i, p i * (ν i (Iio x)).toReal)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (q : ι → ℝ) (hq : q ∈ Feasible p t) :
    (⨅ i, ⨅ (_ : q i ≠ 1), quantile (ν i) (q i)) ≤ quantile μ t := by
  by_contra! hn
  obtain ⟨x, hx, hxmin⟩ := EReal.exists_between_coe_real hn
  have hbound : ∀ i, (ν i (Iio x)).toReal * p i ≤ q i * p i := by
    intro i
    by_cases hpi : 0 < p i
    · let := hprob i hpi
      apply mul_le_mul_of_nonneg_right _ (hp i)
      by_cases hqi : q i = 1
      · rw [hqi]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one :
          ν i (Iio x) ≤ 1))
      · have hi : (x : EReal) ≤ quantile (ν i) (q i) :=
          hxmin.le.trans (iInf_le_of_le i (iInf_le _ hqi))
        exact ((quantile_ge_iff (ν i) (hT i) (hν i) (hq.1 i) x).mp hi).elim
          le_of_lt (fun hz => hz ▸ (hq.1 i).1)
    · have hpi0 := le_antisymm (le_of_not_gt hpi) (hp i)
      simp [hpi0]
  have htotal : (μ (Iio x)).toReal ≤ ∑ i, p i * q i := by
    rw [hmix]
    exact Finset.sum_le_sum fun i _ => by simpa [mul_comm] using hbound i
  have htail : (μ (Iio x)).toReal < t ∨ (μ (Iio x)).toReal = 0 :=
    hq.2.elim (fun h => Or.inl (htotal.trans_lt h))
      (fun h => Or.inr (le_antisymm (h ▸ htotal) ENNReal.toReal_nonneg))
  exact (not_le_of_gt hx) ((quantile_ge_iff μ hS hsupport ht x).mpr htail)

/-- Allocate just above the conditional strict-tail probabilities when the
mixture has positive lower-tail mass. Zero-mass branches cost nothing. -/
private theorem exists_branch_allocation {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) (ν : ι → Measure ℝ)
    (hprob : ∀ i, 0 < p i → IsProbabilityMeasure (ν i))
    (T : ι → Set ℝ) (hT : ∀ i, (T i).Finite) (hν : ∀ i, ν i (T i)ᶜ = 0)
    (t x : ℝ) (hmass : (∑ i, p i * (ν i (Iio x)).toReal) < t ∨
      (∑ i, p i * (ν i (Iio x)).toReal) = 0) :
    ∃ q ∈ Feasible p t, (x : EReal) ≤ ⨅ i, ⨅ (_ : q i ≠ 1), quantile (ν i) (q i) := by
  classical
  let a : ι → ℝ := fun i => (ν i (Iio x)).toReal
  let m : ℝ := ∑ i, p i * a i
  have ha0 : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  let ε := if m = 0 then 0 else (t - m) / 2
  have hε : 0 ≤ ε := by
    by_cases hm : m = 0
    · simp [ε, hm]
    · have hm' : m < t := hmass.resolve_right hm
      simp only [ε, if_neg hm]
      linarith
  let q : ι → ℝ := fun i => if p i = 0 then 1 else min 1 (a i + ε)
  have hq : ∀ i, q i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : p i = 0
    · simp [q, hi]
    · exact ⟨by simpa [q, hi, le_min_iff] using add_nonneg (ha0 i) hε,
        by simp [q, hi]⟩
  have hbudget : ∑ i, p i * q i ≤ m + ε := by
    calc
      ∑ i, p i * q i ≤ ∑ i, p i * (a i + ε) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : p i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (by simp [q, hi]) (hp i)
      _ = m + ε := by simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum, m]
  have hfeas : q ∈ Feasible p t := by
    refine ⟨hq, ?_⟩
    by_cases hm : m = 0
    · right
      have h0 : 0 ≤ ∑ i, p i * q i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hq i).1
      exact le_antisymm (by simpa [ε, hm] using hbudget) h0
    · left
      have hm' : m < t := hmass.resolve_right hm
      have : m + ε < t := by simp only [ε, if_neg hm]; linarith
      exact hbudget.trans_lt this
  refine ⟨q, hfeas, le_iInf fun i => le_iInf fun hi => ?_⟩
  have hpne : p i ≠ 0 := fun hz => hi (by simp [q, hz])
  have hpos := lt_of_le_of_ne (hp i) (Ne.symm hpne)
  let := hprob i hpos
  apply (quantile_ge_iff (ν i) (hT i) (hν i) (hq i) x).mpr
  change a i < q i ∨ a i = 0
  by_cases hm : m = 0
  · right
    have hle : p i * a i ≤ m :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hp j) (ha0 j)) (Finset.mem_univ i)
    rw [hm] at hle
    exact le_antisymm (nonpos_of_mul_nonpos_right hle hpos) (ha0 i)
  · left
    have hm' : m < t := hmass.resolve_right hm
    have hepos : 0 < ε := by simp only [ε, if_neg hm]; linarith
    have hlt : a i + ε < 1 := by
      by_contra! h
      exact hi (by simp [q, hpne, min_eq_left h])
    rw [show q i = a i + ε by simp [q, hpne, min_eq_right hlt.le]]
    linarith

end QuantileMDP

open QuantileMDP

/-- Finite-support mixture quantiles with the strict budget in Prove2Me's
formulation of Li, Zhong and Brandeau, Lemma 2. -/
theorem solution {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hXfin : ∀ i, (Set.range (X i)).Finite) (hY : ∀ i, Measurable (Y i))
    (hY01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hYsum : ∀ ω, ∑ i, Y i ω = 1)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    quantile (P.map (fun ω => ∑ i, X i ω * Y i ω)) τ =
        opt (fun i => (P {ω | Y i ω = 1}).toReal)
          (fun i q => quantile ((P[|{ω | Y i ω = 1}]).map (X i)) q) τ ∧
      OptAttained (fun i => (P {ω | Y i ω = 1}).toReal)
        (fun i q => quantile ((P[|{ω | Y i ω = 1}]).map (X i)) q) τ := by
  classical
  let A : ι → Set Ω := fun i => {ω | Y i ω = 1}
  let p : ι → ℝ := fun i => (P (A i)).toReal
  let ν : ι → Measure ℝ := fun i => (P[|A i]).map (X i)
  let Z : Ω → ℝ := fun ω => ∑ i, X i ω * Y i ω
  let μ := P.map Z
  change quantile μ τ = opt p (fun i => quantile (ν i)) τ ∧
    OptAttained p (fun i => quantile (ν i)) τ
  have hA : ∀ i, MeasurableSet (A i) := fun i => (hY i) (measurableSet_singleton 1)
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have htwo : ∑ k ∈ ({i, j} : Finset ι), Y k ω = 2 := by
      change Y i ω = 1 at hi
      change Y j ω = 1 at hj
      norm_num [Finset.sum_pair hij, hi, hj]
    have hle : ∑ k ∈ ({i, j} : Finset ι), Y k ω ≤ ∑ k, Y k ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ =>
        (hY01 k ω).elim (fun h => h ▸ le_rfl) (fun h => h ▸ zero_le_one)
    rw [htwo, hYsum] at hle
    linarith
  have hcover : ⋃ i, A i = univ := by
    refine eq_univ_of_forall fun ω => mem_iUnion.mpr ?_
    by_contra! hn
    have hzero : ∀ i, Y i ω = 0 := fun i => (hY01 i ω).resolve_right (hn i)
    simpa [hzero] using hYsum ω
  have hZ : Measurable Z :=
    Finset.measurable_fun_sum _ (fun i _ => (hX i).mul (hY i))
  let := Measure.isProbabilityMeasure_map (μ := P) hZ.aemeasurable
  have hZeq (i : ι) (ω : Ω) (hi : ω ∈ A i) : Z ω = X i ω := by
    have hi1 : Y i ω = 1 := hi
    calc
      Z ω = X i ω * Y i ω := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hj : Y j ω ≠ 1 := fun h =>
            (Set.disjoint_left.mp (hdisj hji)) h hi
          rw [(hY01 j ω).resolve_right hj, mul_zero]
        · simp
      _ = X i ω := by rw [hi1, mul_one]
  have hp : ∀ i, 0 ≤ p i := fun _ => ENNReal.toReal_nonneg
  have hp_sum : ∑ i, p i = 1 := by
    have huniv := partition_sum P A hA hdisj hcover univ MeasurableSet.univ
    simp only [inter_univ, measure_univ] at huniv
    change ∑ i, (P (A i)).toReal = 1
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top P (A i)), ← huniv]
    simp
  have hprob : ∀ i, 0 < p i → IsProbabilityMeasure (ν i) := by
    intro i hi
    have hne : P (A i) ≠ 0 := fun hz => (ne_of_gt hi) (by simp [p, hz])
    let := cond_isProbabilityMeasure hne
    exact Measure.isProbabilityMeasure_map (hX i).aemeasurable
  let S := ⋃ i, range (X i)
  have hS : S.Finite := finite_iUnion hXfin
  have hμ : μ Sᶜ = 0 := by
    have hpre : Z ⁻¹' Sᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      obtain ⟨i, hi⟩ := mem_iUnion.mp (show ω ∈ ⋃ i, A i by simp [hcover])
      exact hω (mem_iUnion.mpr ⟨i, ω, hZeq i ω hi |>.symm⟩)
    rw [Measure.map_apply hZ hS.measurableSet.compl, hpre, measure_empty]
  have hν : ∀ i, ν i (range (X i))ᶜ = 0 := by
    intro i
    rw [Measure.map_apply (hX i) (hXfin i).measurableSet.compl]
    simp
  have hmix (x : ℝ) : (μ (Iio x)).toReal = ∑ i, p i * (ν i (Iio x)).toReal := by
    have hpart := partition_sum P A hA hdisj hcover (Z ⁻¹' Iio x) (hZ measurableSet_Iio)
    rw [Measure.map_apply hZ measurableSet_Iio, hpart, ENNReal.toReal_sum (fun i _ =>
      measure_ne_top P (A i ∩ Z ⁻¹' Iio x))]
    apply Finset.sum_congr rfl
    intro i _
    have hsets : A i ∩ Z ⁻¹' Iio x = A i ∩ X i ⁻¹' Iio x := by
      ext ω
      constructor
      · rintro ⟨hA', hZ'⟩
        exact ⟨hA', by
          change X i ω < x
          rw [← hZeq i ω hA']
          exact hZ'⟩
      · rintro ⟨hA', hX'⟩
        exact ⟨hA', by
          change Z ω < x
          rw [hZeq i ω hA']
          exact hX'⟩
    rw [hsets]
    change (P (A i ∩ X i ⁻¹' Iio x)).toReal =
      (P (A i)).toReal * (((P[|A i]).map (X i)) (Iio x)).toReal
    rw [Measure.map_apply (hX i) measurableSet_Iio, ← ENNReal.toReal_mul, mul_comm,
      cond_mul_eq_inter (hA i)]
  obtain ⟨x, hx⟩ := quantile_eq_coe μ hS hμ hτ
  have hmass := (quantile_ge_iff μ hS hμ hτ x).mp hx.ge
  rw [hmix] at hmass
  obtain ⟨q, hq, hqge⟩ :=
    exists_branch_allocation p hp hp_sum ν hprob (fun i => range (X i)) hXfin hν τ x hmass
  have hupper (r : ι → ℝ) (hr : r ∈ Feasible p τ) :
      (⨅ i, ⨅ (_ : r i ≠ 1), quantile (ν i) (r i)) ≤ quantile μ τ :=
    branch_min_le μ hS hμ p hp ν hprob (fun i => range (X i)) hXfin hν hmix hτ r hr
  have hopt : quantile μ τ = opt p (fun i => quantile (ν i)) τ := by
    apply le_antisymm
    · exact hx.le.trans (hqge.trans (le_iSup_of_le q (le_iSup_of_le hq le_rfl)))
    · exact iSup_le fun r => iSup_le fun hr => hupper r hr
  exact ⟨hopt, ⟨q, hq, le_antisymm ((hupper q hq).trans hopt.le)
    (hopt.ge.trans (hx.le.trans hqge))⟩⟩
