-- Prove2me | solution 1 for WangMinimaxRegret.Reformulation.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:33:53.133985+00:00
-- url     : https://prove2.me/submissions/f14e44ee-2695-41c0-a5f3-74111b994476

import Definitions.Def_WangMinimaxRegret_Reformulation_Revenue

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

open WangMinimaxRegret.Reformulation

lemma s225mb_int_nonneg (d : Data) {p : ℝ} (hp : p ∈ interval d) : 0 ≤ p :=
  le_trans d.nonneg_a hp.1

lemma s225mb_ereal_le (x : ℝ) (hx : 0 ≤ x) (e : ℝ≥0∞) :
    (x : EReal) ≤ (e : EReal) ↔ ENNReal.ofReal x ≤ e := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hx]

/-- Feasibility of a ratio in the competitive-ratio supremum, pointwise in p. -/
lemma s225mb_K (d : Data) (m : StieltjesFunction ℝ) (r : ℝ≥0) :
    (∀ F : Measure ℝ, Ambiguous d F → ∀ p ∈ interval d, (r : ℝ≥0∞) * priceRevenue F p ≤ revenue m F) ↔
    ∀ p ∈ interval d, (r : ℝ≥0∞) * ENNReal.ofReal p ≤ fractionalValue {F | Ambiguous d F} m p := by
  constructor
  · intro h p hp
    refine le_iInf₂ fun F hF => le_iInf fun ht => ?_
    have hprob : IsProbabilityMeasure F := hF.1.1
    have htop : tail F p ≠ ∞ := measure_ne_top F _
    rw [ENNReal.le_div_iff_mul_le (Or.inl ht.ne') (Or.inl htop)]
    have := h F hF p hp
    unfold priceRevenue at this
    rwa [mul_assoc]
  · intro h F hF p hp
    have hprob : IsProbabilityMeasure F := hF.1.1
    unfold priceRevenue
    rcases eq_or_ne (tail F p) 0 with ht | ht
    · rw [ht, mul_zero, mul_zero]; positivity
    · have htop : tail F p ≠ ∞ := measure_ne_top F _
      have h1 := h p hp
      have h2 : fractionalValue {F | Ambiguous d F} m p ≤ revenue m F / tail F p :=
        (iInf₂_le F hF).trans (iInf_le _ (pos_iff_ne_zero.mpr ht))
      have h3 := h1.trans h2
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl htop)] at h3
      rwa [← mul_assoc]

lemma s225mb_part1 (d : Data) (m : StieltjesFunction ℝ) (r : ℝ) (hm : IsPayment d m) :
    HypographFeasible d m r ↔ (r : EReal) ≤ (competitiveRatio d m : EReal) := by
  unfold HypographFeasible
  rcases lt_or_ge r 0 with hr | hr
  · constructor
    · intro _
      exact le_trans (EReal.coe_le_coe_iff.mpr hr.le) (EReal.coe_ennreal_nonneg _)
    · intro _
      refine ⟨hm, fun p hp => ?_⟩
      have : r * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr.le (s225mb_int_nonneg d hp)
      exact le_trans (EReal.coe_le_coe_iff.mpr this) (EReal.coe_ennreal_nonneg _)
  · have hiff : (∀ p ∈ interval d, ((r * p : ℝ) : EReal) ≤
        (fractionalValue {F | Ambiguous d F} m p : EReal)) ↔
        ∀ p ∈ interval d, (r.toNNReal : ℝ≥0∞) * ENNReal.ofReal p ≤
          fractionalValue {F | Ambiguous d F} m p := by
      refine forall₂_congr fun p hp => ?_
      rw [s225mb_ereal_le _ (mul_nonneg hr (s225mb_int_nonneg d hp)),
        ENNReal.ofReal_mul hr]
      rfl
    rw [s225mb_ereal_le r hr]
    simp only [hm, true_and]
    rw [hiff, ← s225mb_K]
    constructor
    · intro h
      exact le_iSup₂_of_le (f := fun (r' : ℝ≥0) (_ : ∀ F : Measure ℝ, Ambiguous d F →
        ∀ p ∈ interval d, (r' : ℝ≥0∞) * priceRevenue F p ≤ revenue m F) => (r' : ℝ≥0∞))
        r.toNNReal h le_rfl
    · intro h
      rw [s225mb_K]
      intro p hp
      -- all smaller ratios are feasible
      have hsmall : ∀ c : ℝ≥0, c < r.toNNReal →
          (c : ℝ≥0∞) * ENNReal.ofReal p ≤ fractionalValue {F | Ambiguous d F} m p := by
        intro c hc
        have hlt : (c : ℝ≥0∞) < competitiveRatio d m :=
          lt_of_lt_of_le (by
            rw [show ENNReal.ofReal r = (r.toNNReal : ℝ≥0∞) from rfl]; exact_mod_cast hc) h
        unfold competitiveRatio at hlt
        rw [lt_iSup_iff] at hlt
        obtain ⟨c', hc'⟩ := hlt
        rw [lt_iSup_iff] at hc'
        obtain ⟨hfeas, hcc⟩ := hc'
        exact (s225mb_K d m c).mp (fun F hF q hq =>
          le_trans (by gcongr) (hfeas F hF q hq)) p hp
      apply ENNReal.le_of_forall_nnreal_lt
      intro c hc
      have hp0 := s225mb_int_nonneg d hp
      rcases eq_or_lt_of_le hp0 with hpz | hppos
      · rw [← hpz, ENNReal.ofReal_zero, mul_zero] at hc
        exact absurd hc (by simp)
      · set pn := p.toNNReal
        have hpn : ENNReal.ofReal p = (pn : ℝ≥0∞) := rfl
        have hpn0 : pn ≠ 0 := by
          intro h0; rw [Real.toNNReal_eq_zero] at h0; linarith
        rw [hpn, ← ENNReal.coe_mul, ENNReal.coe_lt_coe] at hc
        have hlt : c / pn < r.toNNReal := (div_lt_iff₀ (pos_iff_ne_zero.mpr hpn0)).mpr hc
        have := hsmall (c / pn) hlt
        rwa [hpn, ← ENNReal.coe_mul, div_mul_cancel₀ c hpn0] at this

lemma s225mb_sup_le_self (e : EReal) :
    (⨆ r : ℝ, ⨆ (_ : (r : EReal) ≤ e), (r : EReal)) = e := by
  apply le_antisymm
  · exact iSup₂_le fun r h => h
  · induction e using EReal.rec with
    | bot => exact bot_le
    | coe x => exact le_iSup₂_of_le (f := fun (r : ℝ) (_ : (r : EReal) ≤ (x : EReal)) =>
        (r : EReal)) x le_rfl le_rfl
    | top =>
      have : ∀ R : ℝ, (R : EReal) ≤ ⨆ r : ℝ, ⨆ (_ : (r : EReal) ≤ ⊤), (r : EReal) :=
        fun R => le_iSup₂_of_le (f := fun (r : ℝ) (_ : (r : EReal) ≤ ⊤) => (r : EReal))
          R le_top le_rfl
      generalize (⨆ r : ℝ, ⨆ (_ : (r : EReal) ≤ ⊤), (r : EReal)) = S at this ⊢
      induction S using EReal.rec with
      | bot => exact absurd (this 0) (by simp)
      | coe x =>
        have := this (x + 1)
        rw [EReal.coe_le_coe_iff] at this; linarith
      | top => exact le_rfl

lemma s225mb_part3 (d : Data) (m : StieltjesFunction ℝ)
    (hb : ∀ F : Measure ℝ, Ambiguous d F → 0 < benchmark d F ∧ benchmark d F < ⊤) :
    competitiveRatio d m = quotientRatio d m := by
  have hfeas : ∀ r : ℝ≥0, (∀ F : Measure ℝ, Ambiguous d F →
      ∀ p ∈ interval d, (r : ℝ≥0∞) * priceRevenue F p ≤ revenue m F) ↔
      (r : ℝ≥0∞) ≤ quotientRatio d m := by
    intro r
    unfold quotientRatio
    rw [le_iInf₂_iff]
    refine forall₂_congr fun F hF => ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (hb F hF).1.ne') (Or.inl (hb F hF).2.ne)]
    unfold benchmark
    rw [mul_comm, ENNReal.iSup_mul, iSup_le_iff]
    refine forall_congr' fun p => ?_
    rw [ENNReal.iSup_mul, iSup_le_iff]
    refine forall_congr' fun _ => ?_
    rw [mul_comm]
  unfold competitiveRatio
  simp_rw [hfeas]
  apply le_antisymm
  · exact iSup₂_le fun r h => h
  · apply ENNReal.le_of_forall_nnreal_lt
    intro c hc
    exact le_iSup₂_of_le (f := fun (r : ℝ≥0) (_ : (r : ℝ≥0∞) ≤ quotientRatio d m) =>
      (r : ℝ≥0∞)) c hc.le le_rfl

lemma s225mb_usc (F : Measure ℝ) [IsFiniteMeasure F] (s : Set ℝ) (hs : ∀ x ∈ s, 0 ≤ x) :
    UpperSemicontinuousOn (fun p : ℝ => p * F.real (Ici p)) s := by
  intro x hx y hy
  set G := F.real (Ici x) with hG
  have hG0 : 0 ≤ G := measureReal_nonneg
  have hx0 := hs x hx
  set D := y - x * G with hD
  have hDpos : 0 < D := by simp only at hy; linarith
  set η := min 1 (D / (2 * (x + G + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 * (x + G + 1)) ≤ D := by
    have : η ≤ D / (2 * (x + G + 1)) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  have hprod : (x + η) * (G + η) < y := by nlinarith
  -- continuity from above of the tail
  have hinter : (⋂ n : ℕ, Ici (x - 1 / ((n : ℝ) + 1))) = Ici x := by
    ext z
    simp only [mem_iInter, mem_Ici]
    constructor
    · intro h
      by_contra hz
      push Not at hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
      have := h n
      linarith
    · intro hz n
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hanti : Antitone (fun n : ℕ => Ici (x - 1 / ((n : ℝ) + 1))) := by
    intro i j hij z hz
    simp only [mem_Ici] at hz ⊢
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    linarith
  have ht := tendsto_measure_iInter_atTop (μ := F)
    (fun n => measurableSet_Ici.nullMeasurableSet) hanti ⟨0, measure_ne_top F _⟩
  rw [hinter] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top F (Ici x))).comp ht
  obtain ⟨n, hn⟩ := (ht'.eventually (gt_mem_nhds (show G < G + η by linarith))).exists
  simp only [Function.comp_apply] at hn
  have hn' : F.real (Ici (x - 1 / ((n : ℝ) + 1))) < G + η := hn
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hnb : Ioo (x - 1 / ((n : ℝ) + 1)) (x + η) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [nhdsWithin_le_nhds hnb, self_mem_nhdsWithin] with z hz hzs
  have hz0 := hs z hzs
  have hmono : F.real (Ici z) ≤ F.real (Ici (x - 1 / ((n : ℝ) + 1))) :=
    measureReal_mono (Ici_subset_Ici.mpr hz.1.le)
  have hGz : 0 ≤ F.real (Ici z) := measureReal_nonneg
  show z * F.real (Ici z) < y
  have h1 : z * F.real (Ici z) ≤ (x + η) * (G + η) := by
    apply mul_le_mul hz.2.le (by linarith) hGz (by linarith)
  linarith

lemma s225mb_part4 (d : Data) (b : ℝ) (F : Measure ℝ) (hb : d.b = (b : WithTop ℝ))
    (hF : Ambiguous d F) : ∃ p ∈ interval d, benchmark d F = priceRevenue F p := by
  have hprob : IsProbabilityMeasure F := hF.1.1
  have hI : interval d = Icc d.a b := by
    ext x; simp only [interval, hb, mem_ofPred_eq, mem_Icc, WithTop.coe_le_coe]
  have hab : d.a ≤ b := by
    have := d.ordered; rw [hb, WithTop.coe_le_coe] at this; exact this
  have hne : (interval d).Nonempty := by rw [hI]; exact nonempty_Icc.mpr hab
  have hcomp : IsCompact (interval d) := by rw [hI]; exact isCompact_Icc
  obtain ⟨p, hp, hmax⟩ := (s225mb_usc F (interval d)
    (fun x hx => s225mb_int_nonneg d hx)).exists_isMaxOn hne hcomp
  have heq : ∀ q ∈ interval d, priceRevenue F q = ENNReal.ofReal (q * F.real (Ici q)) := by
    intro q hq
    unfold priceRevenue tail
    rw [ENNReal.ofReal_mul (s225mb_int_nonneg d hq), Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top F _)]
  refine ⟨p, hp, le_antisymm ?_ (le_iSup₂ (f := fun q (_ : q ∈ interval d) =>
    priceRevenue F q) p hp)⟩
  refine iSup₂_le fun q hq => ?_
  rw [heq q hq, heq p hp]
  exact ENNReal.ofReal_le_ofReal (hmax hq)

theorem solution (d : Data) (hc : Consistent d) :
    (∀ (m : StieltjesFunction ℝ) (r : ℝ), IsPayment d m →
      (HypographFeasible d m r ↔ (r : EReal) ≤ (competitiveRatio d m : EReal))) ∧
    hypographValue d = originalValue d ∧
    (∀ m : StieltjesFunction ℝ, IsPayment d m →
      (∀ F : Measure ℝ, Ambiguous d F → 0 < benchmark d F ∧ benchmark d F < ⊤) →
      competitiveRatio d m = quotientRatio d m) ∧
    (∀ (b : ℝ) (F : Measure ℝ), d.b = (b : WithTop ℝ) → Ambiguous d F →
      ∃ p ∈ interval d, benchmark d F = priceRevenue F p) := by
  refine ⟨fun m r hm => s225mb_part1 d m r hm, ?_, fun m _ hb => s225mb_part3 d m hb,
    fun b F hb hF => s225mb_part4 d b F hb hF⟩
  unfold hypographValue originalValue
  refine iSup_congr fun m => ?_
  by_cases hm : IsPayment d m
  · have : ∀ r : ℝ, HypographFeasible d m r ↔ (r : EReal) ≤ (competitiveRatio d m : EReal) :=
      fun r => s225mb_part1 d m r hm
    simp_rw [this]
    rw [s225mb_sup_le_self, iSup_pos hm]
  · have : ∀ r : ℝ, ¬ HypographFeasible d m r := fun r h => hm h.1
    simp [this, hm]
