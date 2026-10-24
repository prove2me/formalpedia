-- Prove2me | solution 1 for RetailerMarketplace.UnitFee.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T19:35:33.821766+00:00
-- url     : https://prove2.me/submissions/9702c85e-2531-4a46-bc80-ddafa29cfdb0

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

set_option autoImplicit false

open MeasureTheory Set

namespace LB1

open RetailerMarketplace.UnitFee

lemma cdf_cont (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ x, ν {x} = 0) :
    Continuous (ProbabilityTheory.cdf ν) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(ProbabilityTheory.cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have h1 := (ProbabilityTheory.cdf ν).measure_singleton x
  rw [ProbabilityTheory.measure_cdf, h x] at h1
  have h2 : Function.leftLim (ProbabilityTheory.cdf ν) x ≤ ProbabilityTheory.cdf ν x :=
    (ProbabilityTheory.cdf ν).mono.leftLim_le le_rfl
  have h3 := ENNReal.ofReal_eq_zero.1 h1.symm
  linarith

lemma ioi_real_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Ioi x) = 1 - ProbabilityTheory.cdf ν x := by
  rw [ProbabilityTheory.cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic,
    probReal_univ]

lemma integ_affine (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (α β : ℝ) : Integrable (fun v : ℝ => α * v + β) μ :=
  (hint.const_mul α).add (integrable_const β)

lemma integ_SBT (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (f t : ℝ) : Integrable (piSBT_M f t) μ :=
  (integ_affine μ hint f t).congr (ae_of_all _ (fun v => by simp [piSBT_M]))

lemma integ_SBMT (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c f t lam : ℝ) : Integrable (piSBMT_M c f t lam) μ := by
  refine (integ_affine μ hint (lam + (1 - lam) * f * (lam / (1 - f * (1 - lam))))
    (-(lam * c) + (1 - lam) * (f * ((1 - lam) * (c + t) / (1 - f * (1 - lam))) + t))).congr
    (ae_of_all _ ?_)
  intro v
  simp only [piSBMT_M, pbarT]
  ring

lemma integ_SBM (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c : ℝ) : Integrable (RetailerMarketplace.Entry.piSBM c) μ :=
  (integ_affine μ hint 1 (-c)).congr
    (ae_of_all _ (fun v => by simp [RetailerMarketplace.Entry.piSBM]; ring))

lemma mp_meas (c f t : ℝ) : MeasurableSet (mp c f t) := by
  show MeasurableSet {v : ℝ | c + t ≤ v * (1 - f)}
  exact measurableSet_le measurable_const (measurable_id.mul_const _)

noncomputable def Qf (c f t : ℝ) : ℝ → ℝ := (mp c f t).indicator (piSBT_M f t)

noncomputable def Pf (c f t lam : ℝ) : ℝ → ℝ := fun v =>
  (mp c f t).indicator (piSBMT_M c f t lam) v +
    (mp c f t)ᶜ.indicator (RetailerMarketplace.Entry.piSBM c) v

lemma integ_Q (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c f t : ℝ) : Integrable (Qf c f t) μ :=
  (integ_SBT μ hint f t).indicator (mp_meas c f t)

lemma integ_P (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c f t lam : ℝ) : Integrable (Pf c f t lam) μ :=
  ((integ_SBMT μ hint c f t lam).indicator (mp_meas c f t)).add
    ((integ_SBM μ hint c).indicator (mp_meas c f t).compl)

lemma profit_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c f t lam : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    profitM μ c f t lam A
      = ∫ v, Qf c f t v ∂μ + ∫ v in A, (Pf c f t lam v - Qf c f t v) ∂μ := by
  have hm := mp_meas c f t
  have i1 := integ_SBT μ hint f t
  have i2 := integ_SBMT μ hint c f t lam
  have i3 := integ_SBM μ hint c
  rw [integral_sub (integ_P μ hint c f t lam).integrableOn (integ_Q μ hint c f t).integrableOn]
  have e1 : ∫ v, Qf c f t v ∂μ = ∫ v in mp c f t ∩ A, piSBT_M f t v ∂μ
      + ∫ v in mp c f t \ A, piSBT_M f t v ∂μ := by
    simp only [Qf]
    rw [integral_indicator hm, integral_inter_add_sdiff hA i1.integrableOn]
  have e2 : ∫ v in A, Qf c f t v ∂μ = ∫ v in A ∩ mp c f t, piSBT_M f t v ∂μ := by
    simp only [Qf]
    exact setIntegral_indicator hm
  have e3 : ∫ v in A, Pf c f t lam v ∂μ = ∫ v in A ∩ mp c f t, piSBMT_M c f t lam v ∂μ
      + ∫ v in A \ mp c f t, RetailerMarketplace.Entry.piSBM c v ∂μ := by
    simp only [Pf]
    rw [integral_add (i2.indicator hm).integrableOn (i3.indicator hm.compl).integrableOn,
      setIntegral_indicator hm, setIntegral_indicator hm.compl, Set.diff_eq]
  rw [e1, e2, e3, profitM, Set.inter_comm (mp c f t) A]
  ring

lemma mp_eq1 (c fs ts : ℝ) (hf1 : fs < 1) : mp c fs ts = Ici ((c + ts) / (1 - fs)) := by
  ext v
  simp only [mp, mem_setOf_eq, mem_Ici]
  rw [div_le_iff₀ (by linarith)]

lemma mp_eq2 (c fs ts : ℝ) (hc : 0 < c) (hf1 : fs < 1) (ht : 0 ≤ ts) :
    mp c (1 - c * (1 - fs) / (c + ts)) 0 = Ici ((c + ts) / (1 - fs)) := by
  ext v
  simp only [mp, mem_setOf_eq, mem_Ici]
  have ha : 0 < 1 - fs := by linarith
  have hT : 0 < c + ts := by linarith
  rw [div_le_iff₀ ha, show v * (1 - (1 - c * (1 - fs) / (c + ts))) = c * (v * (1 - fs)) / (c + ts)
    by ring, add_zero, le_div_iff₀ hT]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma sbt_diff (c fs ts v : ℝ) (hc : 0 < c) (hf1 : fs < 1) (ht : 0 ≤ ts) :
    piSBT_M (1 - c * (1 - fs) / (c + ts)) 0 v - piSBT_M fs ts v
      = ((1 - fs) * ts / (c + ts)) * (v - (c + ts) / (1 - fs)) := by
  have ha : (1 - fs) ≠ 0 := by intro h; linarith
  have hT : (c + ts) ≠ 0 := by intro h; linarith
  simp only [piSBT_M]
  field_simp
  ring

lemma sbmt_core (c ts fs f' a a' w lam v : ℝ) (hfs : fs = 1 - a) (hf' : f' = 1 - a')
    (hc : c = a' * w) (hts : ts = a * w - a' * w) (ha : 0 < a) (hd1 : 0 < lam + a' * (1 - lam))
    (hd2 : 0 < lam + a * (1 - lam)) :
    piSBMT_M c f' 0 lam v - piSBMT_M c fs ts lam v
      = (1 - lam) * (lam * (a - a') / ((lam + a' * (1 - lam)) * (lam + a * (1 - lam))))
          * (v - w) := by
  subst hfs hf' hc hts
  have e5 : lam + a' * (1 - lam) ≠ 0 := hd1.ne'
  have e6 : lam + a * (1 - lam) ≠ 0 := hd2.ne'
  have p2 : pbarT (a' * w) (1 - a') 0 lam v = w + lam * (v - w) / (lam + a' * (1 - lam)) := by
    simp only [pbarT]
    rw [show 1 - (1 - a') * (1 - lam) = lam + a' * (1 - lam) by ring, div_eq_iff e5, add_mul,
      div_mul_cancel₀ _ e5]
    ring
  have p1 : pbarT (a' * w) (1 - a) (a * w - a' * w) lam v
      = w + lam * (v - w) / (lam + a * (1 - lam)) := by
    simp only [pbarT]
    rw [show 1 - (1 - a) * (1 - lam) = lam + a * (1 - lam) by ring, div_eq_iff e6, add_mul,
      div_mul_cancel₀ _ e6]
    ring
  have key : lam * (a - a') / ((lam + a' * (1 - lam)) * (lam + a * (1 - lam)))
      = lam * ((1 - a') / (lam + a' * (1 - lam)) - (1 - a) / (lam + a * (1 - lam))) := by
    rw [div_sub_div _ _ e5 e6, mul_div_assoc]
    congr 2
    ring
  simp only [piSBMT_M]
  rw [p1, p2, key]
  ring

lemma meas_SBT (f t : ℝ) : Measurable (piSBT_M f t) := by
  show Measurable fun v : ℝ => f * v + t
  fun_prop

lemma meas_SBMT (c f t lam : ℝ) : Measurable (piSBMT_M c f t lam) := by
  show Measurable fun v : ℝ => lam * (v - c) + (1 - lam) * (f * pbarT c f t lam v + t)
  unfold pbarT
  fun_prop

lemma meas_SBM (c : ℝ) : Measurable (RetailerMarketplace.Entry.piSBM c) := by
  show Measurable fun v : ℝ => v - c
  fun_prop

lemma meas_Q (c f t : ℝ) : Measurable (Qf c f t) :=
  (meas_SBT f t).indicator (mp_meas c f t)

lemma meas_P (c f t lam : ℝ) : Measurable (Pf c f t lam) :=
  ((meas_SBMT c f t lam).indicator (mp_meas c f t)).add
    ((meas_SBM c).indicator (mp_meas c f t).compl)

lemma bdd (μ : Measure ℝ) [IsFiniteMeasure μ] (hint : Integrable (fun v : ℝ => v) μ)
    (c f t lam k : ℝ) :
    BddAbove (profitM μ c f t lam '' {A | RetailerMarketplace.Entry.Admissible μ k A}) := by
  refine ⟨∫ v, Qf c f t v ∂μ + ∫ v, |Pf c f t lam v - Qf c f t v| ∂μ, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  rw [profit_eq μ hint c f t lam A hA.1]
  have hi : Integrable (fun v => Pf c f t lam v - Qf c f t v) μ :=
    (integ_P μ hint c f t lam).sub (integ_Q μ hint c f t)
  have h1 : ∫ v in A, (Pf c f t lam v - Qf c f t v) ∂μ
      ≤ ∫ v in A, |Pf c f t lam v - Qf c f t v| ∂μ :=
    setIntegral_mono hi.integrableOn hi.abs.integrableOn (fun v => le_abs_self _)
  have h2 : ∫ v in A, |Pf c f t lam v - Qf c f t v| ∂μ
      ≤ ∫ v, |Pf c f t lam v - Qf c f t v| ∂μ :=
    setIntegral_le_integral hi.abs (ae_of_all _ (fun v => abs_nonneg _))
  linarith

lemma gapA (μ : Measure ℝ) [IsFiniteMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (Q1 Q2 P1 P2 Z : ℝ → ℝ) (iQ1 : Integrable Q1 μ) (iQ2 : Integrable Q2 μ)
    (iP1 : Integrable P1 μ) (iP2 : Integrable P2 μ) (iZ : Integrable Z μ)
    (hZX : ∀ v, Z v ≤ Q2 v - Q1 v) (hY : μ A = 0 ∨ ∀ v, Z v ≤ P2 v - P1 v) :
    (∫ v, Q1 v ∂μ + ∫ v in A, (P1 v - Q1 v) ∂μ) + ∫ v, Z v ∂μ
      ≤ ∫ v, Q2 v ∂μ + ∫ v in A, (P2 v - Q2 v) ∂μ := by
  have iX : Integrable (fun v => Q2 v - Q1 v) μ := iQ2.sub iQ1
  have e1 : ∫ v, (Q2 v - Q1 v) ∂μ = ∫ v, Q2 v ∂μ - ∫ v, Q1 v ∂μ := integral_sub iQ2 iQ1
  have e2 : ∫ v in A, (P2 v - Q2 v) ∂μ = ∫ v in A, P2 v ∂μ - ∫ v in A, Q2 v ∂μ :=
    integral_sub iP2.integrableOn iQ2.integrableOn
  have e3 : ∫ v in A, (P1 v - Q1 v) ∂μ = ∫ v in A, P1 v ∂μ - ∫ v in A, Q1 v ∂μ :=
    integral_sub iP1.integrableOn iQ1.integrableOn
  have e4 : ∫ v in A, (Q2 v - Q1 v) ∂μ = ∫ v in A, Q2 v ∂μ - ∫ v in A, Q1 v ∂μ :=
    integral_sub iQ2.integrableOn iQ1.integrableOn
  have e6 := integral_add_compl hA iX
  have e7 := integral_add_compl hA iZ
  have i1 : ∫ v in Aᶜ, Z v ∂μ ≤ ∫ v in Aᶜ, (Q2 v - Q1 v) ∂μ :=
    setIntegral_mono iZ.integrableOn iX.integrableOn hZX
  rcases hY with h0 | hY
  · have z1 : ∫ v in A, Z v ∂μ = 0 := setIntegral_measure_zero _ h0
    have z2 : ∫ v in A, P2 v ∂μ = 0 := setIntegral_measure_zero _ h0
    have z3 : ∫ v in A, P1 v ∂μ = 0 := setIntegral_measure_zero _ h0
    have z4 : ∫ v in A, Q2 v ∂μ = 0 := setIntegral_measure_zero _ h0
    have z5 : ∫ v in A, Q1 v ∂μ = 0 := setIntegral_measure_zero _ h0
    linarith
  · have e5 : ∫ v in A, (P2 v - P1 v) ∂μ = ∫ v in A, P2 v ∂μ - ∫ v in A, P1 v ∂μ :=
      integral_sub iP2.integrableOn iP1.integrableOn
    have i2 : ∫ v in A, Z v ∂μ ≤ ∫ v in A, (P2 v - P1 v) ∂μ :=
      setIntegral_mono iZ.integrableOn (iP2.sub iP1).integrableOn hY
    linarith

lemma weak_dual (μ : Measure ℝ) [IsFiniteMeasure μ] (A : Set ℝ) (k L : ℝ) (hL : 0 ≤ L)
    (hAk : μ.real A ≤ k) (h : ℝ → ℝ) (hh : Integrable h μ) :
    ∫ v in A, h v ∂μ ≤ ∫ v, max (h v - L) 0 ∂μ + L * k := by
  have i1 : Integrable (fun v => h v - L) μ := hh.sub (integrable_const L)
  have i2 : Integrable (fun v => max (h v - L) 0) μ := i1.pos_part
  have e : ∫ v in A, h v ∂μ = ∫ v in A, (h v - L) ∂μ + μ.real A * L := by
    rw [integral_sub hh.integrableOn (integrable_const L).integrableOn, setIntegral_const,
      smul_eq_mul]
    ring
  have s1 : ∫ v in A, (h v - L) ∂μ ≤ ∫ v in A, max (h v - L) 0 ∂μ :=
    setIntegral_mono i1.integrableOn i2.integrableOn (fun v => le_max_left _ _)
  have s2 : ∫ v in A, max (h v - L) 0 ∂μ ≤ ∫ v, max (h v - L) 0 ∂μ :=
    setIntegral_le_integral i2 (ae_of_all _ (fun v => le_max_right _ _))
  nlinarith

lemma strong_dual (μ : Measure ℝ) [IsFiniteMeasure μ] (L : ℝ) (h : ℝ → ℝ)
    (hh : Integrable h μ) (hm : Measurable h) :
    ∫ v in {v | L < h v}, h v ∂μ
      = ∫ v, max (h v - L) 0 ∂μ + L * μ.real {v | L < h v} := by
  have hS : MeasurableSet {v | L < h v} := measurableSet_lt measurable_const hm
  have e : ∫ v in {v | L < h v}, h v ∂μ
      = ∫ v in {v | L < h v}, (h v - L) ∂μ + μ.real {v | L < h v} * L := by
    rw [integral_sub hh.integrableOn (integrable_const L).integrableOn, setIntegral_const,
      smul_eq_mul]
    ring
  have e2 : ∫ v in {v | L < h v}, (h v - L) ∂μ = ∫ v in {v | L < h v}, max (h v - L) 0 ∂μ := by
    refine setIntegral_congr_fun hS (fun v hv => ?_)
    have : L < h v := hv
    exact (max_eq_left (by linarith)).symm
  have e3 : ∫ v in {v | L < h v}, max (h v - L) 0 ∂μ = ∫ v, max (h v - L) 0 ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => ?_)
    have : ¬ L < h v := hv
    exact max_eq_right (by linarith)
  rw [e, e2, e3]
  ring

lemma exists_level (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hatom : ∀ x, μ (g ⁻¹' {x}) = 0) (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1)
    (h0 : μ.real {v | 0 < g v} = 1) : ∃ L, 0 < L ∧ μ.real {v | L < g v} = k := by
  set ν := μ.map g with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hνa : ∀ x, ν {x} = 0 := fun x => by
    rw [hν, Measure.map_apply hg (measurableSet_singleton x)]; exact hatom x
  have hF : ∀ L, μ.real {v | L < g v} = 1 - ProbabilityTheory.cdf ν L := by
    intro L
    rw [← ioi_real_eq ν L, measureReal_def, measureReal_def, hν,
      Measure.map_apply hg measurableSet_Ioi]
    rfl
  have hcont : Continuous (fun L => 1 - ProbabilityTheory.cdf ν L) :=
    continuous_const.sub (cdf_cont ν hνa)
  have hev := (tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atTop (μ := ν))).1 (1 - k)
    (by linarith)
  obtain ⟨M, hM0, hM⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and hev).exists
  have hsub := intermediate_value_Icc' hM0 hcont.continuousOn
  have hk : k ∈ Icc (1 - ProbabilityTheory.cdf ν M) (1 - ProbabilityTheory.cdf ν 0) := by
    rw [← hF 0, h0]
    constructor <;> linarith
  obtain ⟨L, hL, hLk⟩ := hsub hk
  have hLk' : 1 - ProbabilityTheory.cdf ν L = k := hLk
  refine ⟨L, ?_, by rw [hF L]; exact hLk'⟩
  rcases (eq_or_lt_of_le hL.1) with h | h
  · subst h
    have h00 := hF 0
    linarith
  · exact h

lemma maxlem (x y p L m : ℝ) (hxy : m ≤ x - y) (hxz : m ≤ x - (p - L)) :
    m ≤ (x + max (p - x - L) 0) - (y + max (p - y - L) 0) := by
  simp only [max_def]
  split_ifs <;> linarith

lemma maxlem0 (x y p L : ℝ) (hxy : y ≤ x) :
    0 ≤ (x + max (p - x - L) 0) - (y + max (p - y - L) 0) := by
  simp only [max_def]
  split_ifs <;> linarith

lemma intZ (μ : Measure ℝ) [IsFiniteMeasure μ] (m p q : ℝ) :
    ∫ v, m * (Ioo p q).indicator 1 v ∂μ = m * μ.real (Ioo p q) := by
  rw [integral_const_mul, integral_indicator_one measurableSet_Ioo]

lemma integZ (μ : Measure ℝ) [IsFiniteMeasure μ] (m p q : ℝ) :
    Integrable (fun v => m * (Ioo p q).indicator 1 v) μ :=
  ((integrable_const (1 : ℝ)).indicator measurableSet_Ioo).const_mul m

end LB1

open LB1

set_option maxHeartbeats 1000000 in
open MeasureTheory RetailerMarketplace.UnitFee in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ) (hc : 0 < c)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hint : Integrable (fun v : ℝ => v) μ)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b))
    (hnd : ¬ (k = 1 ∧ lam = 1)) :
    ∀ fs ts : ℝ, IsOptimalFee μ c lam k fs ts → fs < 1 → ts = 0 := by
  intro fs ts hopt hf1
  obtain ⟨⟨hf0, -⟩, ht0, hmax⟩ := hopt
  by_contra hne
  have ht : 0 < ts := lt_of_le_of_ne ht0 (Ne.symm hne)
  obtain ⟨hl0, hl1⟩ := hlam
  obtain ⟨hk0, hk1⟩ := hk
  have ha : 0 < 1 - fs := by linarith
  have hT : 0 < c + ts := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = (c + ts) / (1 - fs) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = c * (1 - fs) / (c + ts) := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f' = 1 - c * (1 - fs) / (c + ts) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = (1 - fs) * ts / (c + ts) := ⟨_, rfl⟩
  have hβpos : 0 < β := by rw [hβ]; positivity
  have ha'pos : 0 < a' := by rw [ha']; positivity
  have hwpos : 0 < w := by rw [hw]; positivity
  have ha'w : c = a' * w := by rw [ha', hw]; field_simp
  have haw : c + ts = (1 - fs) * w := by rw [hw]; field_simp
  have ha'lt : a' < 1 - fs := by rw [ha', div_lt_iff₀ hT]; nlinarith
  have hf'eq : f' = 1 - a' := by rw [hf', ha']
  have hf'0 : 0 ≤ f' := by rw [hf'eq]; linarith
  have hf'1 : f' ≤ 1 := by rw [hf'eq]; linarith
  have hcw : c < w := by nlinarith
  have hm1 : mp c fs ts = Ici w := by rw [hw]; exact mp_eq1 c fs ts hf1
  have hm2 : mp c f' 0 = Ici w := by rw [hw, hf']; exact mp_eq2 c fs ts hc hf1 ht0
  have hQ1 : ∀ v, Qf c fs ts v = if w ≤ v then fs * v + ts else 0 := by
    intro v; simp only [Qf, hm1, Set.indicator_apply, mem_Ici, piSBT_M]
  have hQ2 : ∀ v, Qf c f' 0 v = if w ≤ v then f' * v else 0 := by
    intro v; simp only [Qf, hm2, Set.indicator_apply, mem_Ici, piSBT_M, add_zero]
  have hP1 : ∀ v, Pf c fs ts lam v = if w ≤ v then piSBMT_M c fs ts lam v else v - c := by
    intro v
    simp only [Pf, hm1, Set.indicator_apply, mem_Ici, mem_compl_iff,
      RetailerMarketplace.Entry.piSBM]
    split_ifs <;> simp
  have hP2 : ∀ v, Pf c f' 0 lam v = if w ≤ v then piSBMT_M c f' 0 lam v else v - c := by
    intro v
    simp only [Pf, hm2, Set.indicator_apply, mem_Ici, mem_compl_iff,
      RetailerMarketplace.Entry.piSBM]
    split_ifs <;> simp
  have hX : ∀ v, f' * v - (fs * v + ts) = β * (v - w) := by
    intro v
    have := sbt_diff c fs ts v hc hf1 ht0
    simp only [piSBT_M] at this
    rw [hf', hβ, hw]; linarith
  have hd1 : 0 < lam + a' * (1 - lam) := by nlinarith
  have hd2 : 0 < lam + (1 - fs) * (1 - lam) := by nlinarith
  have hY : ∀ v, piSBMT_M c f' 0 lam v - piSBMT_M c fs ts lam v
      = (1 - lam) * (lam * ((1 - fs) - a') / ((lam + a' * (1 - lam)) * (lam + (1 - fs) * (1 - lam))))
        * (v - w) :=
    fun v => sbmt_core c ts fs f' (1 - fs) a' w lam v (by ring) hf'eq ha'w (by linarith) ha hd1 hd2
  have iQ1 := integ_Q μ hint c fs ts
  have iQ2 := integ_Q μ hint c f' 0
  have iP1 := integ_P μ hint c fs ts lam
  have iP2 := integ_P μ hint c f' 0 lam
  have hPi2 : ∀ B, RetailerMarketplace.Entry.Admissible μ k B →
      profitM μ c f' 0 lam B ≤ PiM μ c f' 0 lam k :=
    fun B hB => le_csSup (bdd μ hint c f' 0 lam k) ⟨B, hB, rfl⟩
  have hδ : ∃ δ > 0, ∀ A, RetailerMarketplace.Entry.Admissible μ k A →
      profitM μ c fs ts lam A + δ ≤ PiM μ c f' 0 lam k := by
    obtain ⟨α, hα⟩ : ∃ α, α = (1 - lam) * (lam * ((1 - fs) - a') /
        ((lam + a' * (1 - lam)) * (lam + (1 - fs) * (1 - lam)))) := ⟨_, rfl⟩
    have hα0 : 0 ≤ α := by
      rw [hα]
      apply mul_nonneg (by linarith)
      apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    have gen : ∀ m : ℝ, 0 < m → m ≤ β → (k = 0 ∨ m ≤ α) → ∃ δ > 0, ∀ A,
        RetailerMarketplace.Entry.Admissible μ k A →
        profitM μ c fs ts lam A + δ ≤ PiM μ c f' 0 lam k := by
      intro m hm hmβ hor
      refine ⟨∫ v, m * (Ioo (w + 1) (w + 2)).indicator 1 v ∂μ, ?_, ?_⟩
      · rw [intZ]
        have h1 := hfull (w + 1) (w + 2) (by linarith) (by linarith)
        have h2 : 0 < μ.real (Ioo (w + 1) (w + 2)) :=
          ENNReal.toReal_pos (ne_of_gt h1) (measure_ne_top _ _)
        positivity
      · intro A hA
        have hZX : ∀ v, m * (Ioo (w + 1) (w + 2)).indicator 1 v ≤ Qf c f' 0 v - Qf c fs ts v := by
          intro v
          rw [hQ1 v, hQ2 v]
          by_cases hv : v ∈ Ioo (w + 1) (w + 2)
          · have hwv : w ≤ v := by linarith [hv.1]
            rw [if_pos hwv, if_pos hwv, hX v, Set.indicator_of_mem hv, Pi.one_apply, mul_one]
            nlinarith [hv.1]
          · rw [Set.indicator_of_notMem hv, mul_zero]
            split_ifs with hwv
            · rw [hX v]; nlinarith
            · simp
        have hYor : μ A = 0 ∨ ∀ v, m * (Ioo (w + 1) (w + 2)).indicator 1 v
            ≤ Pf c f' 0 lam v - Pf c fs ts lam v := by
          rcases hor with hk' | hmα
          · left
            have := hA.2
            rw [hk', ENNReal.ofReal_zero] at this
            exact le_antisymm this zero_le
          · right
            intro v
            rw [hP1 v, hP2 v]
            by_cases hv : v ∈ Ioo (w + 1) (w + 2)
            · have hwv : w ≤ v := by linarith [hv.1]
              rw [if_pos hwv, if_pos hwv, hY v, ← hα, Set.indicator_of_mem hv, Pi.one_apply,
                mul_one]
              nlinarith [hv.1]
            · rw [Set.indicator_of_notMem hv, mul_zero]
              split_ifs with hwv
              · rw [hY v, ← hα]; nlinarith
              · simp
        have h1 := gapA μ A hA.1 (Qf c fs ts) (Qf c f' 0) (Pf c fs ts lam) (Pf c f' 0 lam)
          (fun v => m * (Ioo (w + 1) (w + 2)).indicator 1 v) iQ1 iQ2 iP1 iP2
          (integZ μ m _ _) hZX hYor
        rw [← profit_eq μ hint c fs ts lam A hA.1, ← profit_eq μ hint c f' 0 lam A hA.1] at h1
        linarith [hPi2 A hA]
    by_cases hcase : lam < 1 ∨ k = 0
    · rcases hcase with hl | hk'
      · have hαpos : 0 < α := by
          rw [hα]
          apply mul_pos (by linarith)
          apply div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
        exact gen (min β α) (lt_min hβpos hαpos) (min_le_left _ _) (Or.inr (min_le_right _ _))
      · exact gen β hβpos le_rfl (Or.inl hk')
    · push_neg at hcase
      obtain ⟨hl, hk'⟩ := hcase
      have hl' : lam = 1 := le_antisymm hl1 hl
      subst hl'
      have hk1' : k < 1 := lt_of_le_of_ne hk1 (fun h => hnd ⟨h, rfl⟩)
      have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk')
      have hP1' : ∀ v, Pf c fs ts 1 v = v - c := by
        intro v; rw [hP1 v]; split_ifs <;> simp [piSBMT_M]
      have hP2' : ∀ v, Pf c f' 0 1 v = v - c := by
        intro v; rw [hP2 v]; split_ifs <;> simp [piSBMT_M]
      have hgm : Measurable (fun v => Pf c f' 0 1 v - Qf c f' 0 v) :=
        (meas_P c f' 0 1).sub (meas_Q c f' 0)
      have hgv : ∀ v, Pf c f' 0 1 v - Qf c f' 0 v = if w ≤ v then a' * v - c else v - c := by
        intro v; rw [hP2' v, hQ2 v, hf'eq]; split_ifs <;> ring
      have hatom : ∀ x, μ ((fun v => Pf c f' 0 1 v - Qf c f' 0 v) ⁻¹' {x}) = 0 := by
        intro x
        apply measure_mono_null (t := ({c + x, (c + x) / a'} : Set ℝ))
        · intro v hv
          simp only [mem_preimage, mem_singleton_iff] at hv
          rw [hgv v] at hv
          simp only [mem_insert_iff, mem_singleton_iff]
          split_ifs at hv
          · right; field_simp; linarith
          · left; linarith
        · exact hac ((Set.toFinite _).measure_zero volume)
      have h0 : μ.real {v | 0 < Pf c f' 0 1 v - Qf c f' 0 v} = 1 := by
        have hS0 : MeasurableSet {v | Pf c f' 0 1 v - Qf c f' 0 v ≤ 0} :=
          measurableSet_le hgm measurable_const
        have hnull : μ {v | Pf c f' 0 1 v - Qf c f' 0 v ≤ 0} = 0 := by
          apply measure_mono_null (t := Iio c ∪ ({c, w} : Set ℝ))
          · intro v hv
            simp only [mem_setOf_eq] at hv
            rw [hgv v] at hv
            simp only [mem_union, mem_Iio, mem_insert_iff, mem_singleton_iff]
            split_ifs at hv with hwv
            · right; right
              have : a' * v ≤ a' * w := by linarith
              have := le_of_mul_le_mul_left this ha'pos
              linarith
            · rcases lt_or_eq_of_le (show v ≤ c by linarith) with h | h
              · left; exact h
              · right; left; exact h
          · exact measure_union_null hsupp (hac ((Set.toFinite _).measure_zero volume))
        have hc' : {v | 0 < Pf c f' 0 1 v - Qf c f' 0 v}
            = {v | Pf c f' 0 1 v - Qf c f' 0 v ≤ 0}ᶜ := by
          ext v; simp [not_le]
        rw [hc', measureReal_compl hS0, probReal_univ, measureReal_def, hnull]
        simp
      obtain ⟨L, hL0, hLk⟩ := exists_level μ _ hgm hatom k hkpos hk1' h0
      have hLk' : μ.real {v | L < Pf c f' 0 1 v - Qf c f' 0 v} = k := hLk
      have hS : MeasurableSet {v | L < Pf c f' 0 1 v - Qf c f' 0 v} :=
        measurableSet_lt measurable_const hgm
      have hSadm : RetailerMarketplace.Entry.Admissible μ k
          {v | L < Pf c f' 0 1 v - Qf c f' 0 v} := by
        refine ⟨hS, ?_⟩
        rw [← ofReal_measureReal (measure_ne_top _ _), hLk']
      obtain ⟨e, he⟩ : ∃ e, e = L / (3 * a') := ⟨_, rfl⟩
      have hepos : 0 < e := by rw [he]; positivity
      have hae : a' * e = L / 3 := by rw [he]; field_simp
      obtain ⟨m, hm⟩ : ∃ m, m = min (β * e) (L / 3) := ⟨_, rfl⟩
      have hmpos : 0 < m := by rw [hm]; exact lt_min (by positivity) (by linarith)
      have hmβ : m ≤ β * e := by rw [hm]; exact min_le_left _ _
      have hmL : m ≤ L / 3 := by rw [hm]; exact min_le_right _ _
      refine ⟨∫ v, m * (Ioo (w + e) (w + 2 * e)).indicator 1 v ∂μ, ?_, ?_⟩
      · rw [intZ]
        have h1 := hfull (w + e) (w + 2 * e) (by linarith) (by linarith)
        have h2 : 0 < μ.real (Ioo (w + e) (w + 2 * e)) :=
          ENNReal.toReal_pos (ne_of_gt h1) (measure_ne_top _ _)
        positivity
      · intro A hA
        have iZ := integZ μ m (w + e) (w + 2 * e)
        have ig2 : Integrable (fun v => Pf c f' 0 1 v - Qf c f' 0 v) μ := iP2.sub iQ2
        have ig1 : Integrable (fun v => Pf c fs ts 1 v - Qf c fs ts v) μ := iP1.sub iQ1
        have imax1 : Integrable (fun v => max (Pf c fs ts 1 v - Qf c fs ts v - L) 0) μ :=
          (ig1.sub (integrable_const L)).pos_part
        have imax2 : Integrable (fun v => max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0) μ :=
          (ig2.sub (integrable_const L)).pos_part
        have hAk : μ.real A ≤ k := by
          rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hk0 hA.2
        have hw1 : ∫ v in A, (Pf c fs ts 1 v - Qf c fs ts v) ∂μ
            ≤ ∫ v, max (Pf c fs ts 1 v - Qf c fs ts v - L) 0 ∂μ + L * k :=
          weak_dual μ A k L hL0.le hAk _ ig1
        have hsd : ∫ v in {v | L < Pf c f' 0 1 v - Qf c f' 0 v}, (Pf c f' 0 1 v - Qf c f' 0 v) ∂μ
            = ∫ v, max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0 ∂μ
              + L * μ.real {v | L < Pf c f' 0 1 v - Qf c f' 0 v} :=
          strong_dual μ L _ ig2 hgm
        have hpt : ∀ v, Qf c fs ts v + max (Pf c fs ts 1 v - Qf c fs ts v - L) 0
            + m * (Ioo (w + e) (w + 2 * e)).indicator 1 v
            ≤ Qf c f' 0 v + max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0 := by
          intro v
          rw [hQ1 v, hQ2 v, hP1' v, hP2' v]
          by_cases hv : v ∈ Ioo (w + e) (w + 2 * e)
          · have hwv : w ≤ v := by linarith [hv.1]
            rw [if_pos hwv, if_pos hwv, Set.indicator_of_mem hv, Pi.one_apply, mul_one]
            have hxy : m ≤ f' * v - (fs * v + ts) := by
              rw [hX v]; nlinarith [hv.1]
            have hxz : m ≤ f' * v - (v - c - L) := by
              rw [hf'eq]; nlinarith [hv.2]
            have := maxlem (f' * v) (fs * v + ts) (v - c) L m hxy hxz
            linarith
          · rw [Set.indicator_of_notMem hv, mul_zero]
            split_ifs with hwv
            · have := maxlem0 (f' * v) (fs * v + ts) (v - c) L (by nlinarith [hX v])
              linarith
            · have := maxlem0 0 0 (v - c) L le_rfl
              linarith
        have s1 : ∫ v, (Qf c fs ts v + max (Pf c fs ts 1 v - Qf c fs ts v - L) 0
            + m * (Ioo (w + e) (w + 2 * e)).indicator 1 v) ∂μ
            = ∫ v, (Qf c fs ts v + max (Pf c fs ts 1 v - Qf c fs ts v - L) 0) ∂μ
              + ∫ v, m * (Ioo (w + e) (w + 2 * e)).indicator 1 v ∂μ :=
          integral_add (iQ1.add imax1) iZ
        have s2 : ∫ v, (Qf c fs ts v + max (Pf c fs ts 1 v - Qf c fs ts v - L) 0) ∂μ
            = ∫ v, Qf c fs ts v ∂μ + ∫ v, max (Pf c fs ts 1 v - Qf c fs ts v - L) 0 ∂μ :=
          integral_add iQ1 imax1
        have s3 : ∫ v, (Qf c f' 0 v + max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0) ∂μ
            = ∫ v, Qf c f' 0 v ∂μ + ∫ v, max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0 ∂μ :=
          integral_add iQ2 imax2
        have mono : ∫ v, (Qf c fs ts v + max (Pf c fs ts 1 v - Qf c fs ts v - L) 0
            + m * (Ioo (w + e) (w + 2 * e)).indicator 1 v) ∂μ
            ≤ ∫ v, (Qf c f' 0 v + max (Pf c f' 0 1 v - Qf c f' 0 v - L) 0) ∂μ :=
          integral_mono ((iQ1.add imax1).add iZ) (iQ2.add imax2) (fun v => hpt v)
        have pA := profit_eq μ hint c fs ts 1 A hA.1
        have pS := profit_eq μ hint c f' 0 1 _ hS
        have hS2 := hPi2 _ hSadm
        rw [hLk'] at hsd
        linarith
  obtain ⟨δ, hδpos, hδA⟩ := hδ
  have hne_img : (profitM μ c fs ts lam '' {A | RetailerMarketplace.Entry.Admissible μ k A}).Nonempty :=
    ⟨_, ∅, ⟨MeasurableSet.empty, by simp⟩, rfl⟩
  have hsup : PiM μ c fs ts lam k ≤ PiM μ c f' 0 lam k - δ := by
    apply csSup_le hne_img
    rintro _ ⟨A, hA, rfl⟩
    linarith [hδA A hA]
  have := hmax f' ⟨hf'0, hf'1⟩ 0 le_rfl
  linarith
