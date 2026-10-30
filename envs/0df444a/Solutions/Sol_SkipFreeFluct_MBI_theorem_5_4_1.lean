-- Prove2me | solution 1 for SkipFreeFluct.MBI.theorem_5_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:06:15.69711+00:00
-- url     : https://prove2.me/submissions/ca4d3b03-bd7c-4db8-8821-907c7362256e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
import Theorems.Thm_SkipFreeFluct_MBI_lemma_5_1
import Theorems.Thm_SkipFreeFluct_MBI_lemma_5_2
import Theorems.Thm_SkipFreeFluct_MBI_transition_tsum_le_one
import Theorems.Thm_SkipFreeFluct_MBI_mbiQ_skipFree_QMatrix
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_gf
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_1_mbp
open scoped ENNReal Topology
open Filter MeasureTheory

namespace MBI541
open SkipFreeFluct.MBI Finset ProbabilityTheory

lemma psi_continuousOn (P : MBIParams) (hP : P.Valid) : ContinuousOn (psi P) (Set.Icc 0 1) := by
  obtain ⟨_, hmu, hmu1, _⟩ := hP
  have hser : ContinuousOn (fun s : ℝ => ∑' j : ℕ, P.mu j * s ^ j) (Set.Icc 0 1) := by
    refine continuousOn_tsum (u := P.mu) (fun j => by fun_prop) hmu1.summable (fun j s hs => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hmu j), norm_pow, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_right (hmu j) (pow_le_one₀ hs.1 hs.2)
  unfold psi
  exact (continuousOn_const.mul (hser.sub continuousOn_id)).sub
    (continuousOn_const.mul continuousOn_id)

lemma psi_zero (P : MBIParams) (hP : P.Valid) : psi P 0 = P.alpha * P.mu 0 := by
  unfold psi
  rw [tsum_eq_single 0 (fun j hj => by simp [zero_pow hj])]
  simp

lemma zero_set_nonempty (P : MBIParams) (hP : P.Valid) :
    ({s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ psi P s = 0}).Nonempty := by
  have hc := psi_continuousOn P hP
  have h0 := psi_zero P hP
  obtain ⟨hα, hmu, hmu1, hmu0, _, hp, _⟩ := hP
  have h1 : psi P 1 = -P.p := by
    unfold psi
    simp only [one_pow, mul_one]
    rw [hmu1.tsum_eq]; ring
  have hpos0 : 0 < psi P 0 := by rw [h0]; positivity
  obtain ⟨c, hcI, hc0⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, psi P c = 0 :=
    intermediate_value_Icc' zero_le_one hc ⟨by rw [h1]; linarith, hpos0.le⟩
  have hcne : c ≠ 0 := by rintro rfl; linarith
  exact ⟨c, ⟨lt_of_le_of_ne hcI.1 (Ne.symm hcne), hcI.2⟩, hc0⟩

lemma s0_le_one (P : MBIParams) (hP : P.Valid) : s0 P ≤ 1 := by
  obtain ⟨c, hc⟩ := zero_set_nonempty P hP
  exact (csInf_le ⟨0, fun s hs => hs.1.1.le⟩ hc).trans hc.1.2

lemma s0_pos (P : MBIParams) (hP : P.Valid) : 0 < s0 P := by
  have hc := psi_continuousOn P hP
  have hpos0 : 0 < psi P 0 := by rw [psi_zero P hP]; have := hP.1; have := hP.2.2.2.1; positivity
  have hev : ∀ᶠ s in 𝓝[Set.Icc 0 1] (0 : ℝ), 0 < psi P s :=
    (hc 0 ⟨le_rfl, zero_le_one⟩).eventually (lt_mem_nhds hpos0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine lt_of_lt_of_le hε (le_csInf (zero_set_nonempty P hP) fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  have : 0 < psi P s := hball ⟨by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1.1]; exact hlt,
    ⟨hs.1.1.le, hs.1.2⟩⟩
  linarith [hs.2]

lemma psi_pos (P : MBIParams) (hP : P.Valid) : ∀ v ∈ Set.Ico 0 (s0 P), 0 < psi P v := by
  intro v hv
  have hc := psi_continuousOn P hP
  have hpos0 : 0 < psi P 0 := by rw [psi_zero P hP]; have := hP.1; have := hP.2.2.2.1; positivity
  have h1 := s0_le_one P hP
  by_contra hle
  push Not at hle
  have hv0 : v ≠ 0 := by rintro rfl; linarith
  obtain ⟨c, hcI, hc0⟩ : ∃ c ∈ Set.Icc (0 : ℝ) v, psi P c = 0 :=
    intermediate_value_Icc' hv.1 (hc.mono (Set.Icc_subset_Icc le_rfl (by linarith [hv.2])))
      ⟨hle, hpos0.le⟩
  have hcne : c ≠ 0 := by rintro rfl; linarith
  have hcmem : c ∈ {s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ psi P s = 0} :=
    ⟨⟨lt_of_le_of_ne hcI.1 (Ne.symm hcne), by linarith [hcI.2, hv.2]⟩, hc0⟩
  have := csInf_le ⟨0, fun s hs => hs.1.1.le⟩ hcmem
  unfold s0 at hv
  linarith [hcI.2, hv.2]

lemma psi_contAt (P : MBIParams) (hP : P.Valid) : ∀ v ∈ Set.Ioo 0 (s0 P), ContinuousAt (psi P) v := by
  intro v hv
  have h1 := s0_le_one P hP
  exact (psi_continuousOn P hP).continuousAt (Icc_mem_nhds hv.1 (by linarith [hv.2]))

lemma inv_psi_continuousOn (P : MBIParams) (hP : P.Valid) (v : ℝ) (hv : v ∈ Set.Ico 0 (s0 P)) :
    ContinuousOn (fun u => 1 / psi P u) (Set.Icc 0 v) := by
  have h1 := s0_le_one P hP
  refine ContinuousOn.div continuousOn_const
    ((psi_continuousOn P hP).mono (Set.Icc_subset_Icc le_rfl (by linarith [hv.2]))) ?_
  intro u hu
  exact (psi_pos P hP u ⟨hu.1, lt_of_le_of_lt hu.2 hv.2⟩).ne'

lemma Lam_hasDerivAt (P : MBIParams) (hP : P.Valid) :
    ∀ v ∈ Set.Ioo 0 (s0 P), HasDerivAt (Lam P) (1 / psi P v) v := by
  intro v hv
  unfold Lam
  have hopen : ContinuousOn (fun u => 1 / psi P u) (Set.Ioo 0 (s0 P)) := by
    intro u hu
    exact ((continuousAt_const.div (psi_contAt P hP u hu)
      (psi_pos P hP u ⟨hu.1.le, hu.2⟩).ne')).continuousWithinAt
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact (inv_psi_continuousOn P hP v ⟨hv.1.le, hv.2⟩).intervalIntegrable_of_Icc hv.1.le
  · exact hopen.stronglyMeasurableAtFilter isOpen_Ioo v hv
  · exact continuousAt_const.div (psi_contAt P hP v hv) (psi_pos P hP v ⟨hv.1.le, hv.2⟩).ne'

lemma Lam_strictMonoOn (P : MBIParams) (hP : P.Valid) : StrictMonoOn (Lam P) (Set.Ico 0 (s0 P)) := by
  intro u hu v hv huv
  unfold Lam
  have hI : ∀ w ∈ Set.Ico 0 (s0 P), IntervalIntegrable (fun u => 1 / psi P u) volume 0 w :=
    fun w hw => (inv_psi_continuousOn P hP w hw).intervalIntegrable_of_Icc hw.1
  rw [← sub_pos, intervalIntegral.integral_interval_sub_left (hI v hv) (hI u hu)]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun w hw => ?_) huv
  · exact ((inv_psi_continuousOn P hP v hv).mono (Set.Icc_subset_Icc hu.1 le_rfl)
      ).intervalIntegrable_of_Icc huv.le
  · exact one_div_pos.mpr (psi_pos P hP w ⟨by linarith [hu.1, hw.1], lt_trans hw.2 hv.2⟩)

instance instProbExp : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

instance instProbClock (n : ℕ) : IsProbabilityMeasure (clockLaw n) := by
  unfold clockLaw; infer_instance

lemma measurable_transition (E : Set ℤ) (Q : ℤ → ℤ → ℝ) (x y : ℤ) :
    Measurable (fun t => transition E Q t x y) := by
  classical
  unfold transition
  by_cases hxy : x ∈ E ∧ y ∈ E
  swap
  · simp only [hxy, if_false]; exact measurable_const
  simp only [hxy, and_self, if_true]
  refine Measurable.ennreal_tsum fun n => Measurable.ennreal_tsum fun ω => ?_
  by_cases hc : ω 0 = x ∧ ω (Fin.last n) = y
  swap
  · simp only [hc, if_false]; exact measurable_const
  simp only [hc, and_self, if_true]
  refine Measurable.const_mul ?_ _
  have hJ : Measurable (fun e : Fin (n + 1) → ℝ => jumpTime Q ω e) := by
    unfold jumpTime holdTime
    exact Finset.measurable_sum _ fun k _ =>
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply _)).div_const _
  have hH : Measurable (fun e : Fin (n + 1) → ℝ => holdTime Q ω e (Fin.last n)) := by
    unfold holdTime
    exact (ENNReal.measurable_ofReal.comp (measurable_pi_apply _)).div_const _
  have hS : MeasurableSet {p : ℝ × (Fin (n + 1) → ℝ) | jumpTime Q ω p.2 ≤ ENNReal.ofReal p.1 ∧
      ENNReal.ofReal p.1 < jumpTime Q ω p.2 + holdTime Q ω p.2 (Fin.last n)} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le (hJ.comp measurable_snd) (ENNReal.measurable_ofReal.comp measurable_fst)
    · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hJ.comp measurable_snd).add (hH.comp measurable_snd))
  exact measurable_measure_prodMk_left (ν := clockLaw n) hS

/-- The generating function of the resolvent (proof of Theorem 5.4(1), p. 16). -/
lemma gf_resolvent (P : MBIParams) (hP : P.Valid) (x : ℕ) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    ∑' y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y * ENNReal.ofReal (s ^ y) =
      ENNReal.ofReal (∑' k, piSeq P k * s ^ k) *
        ∫⁻ v in Set.Ioo s (s0 P), ENNReal.ofReal
          (v ^ x / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u)) := by
  obtain ⟨hnn, hgf⟩ := lemma_5_1 P hP
  obtain ⟨hbij, hgen⟩ := lemma_5_2 P hP
  have hpi : ∀ k, 0 ≤ piSeq P k := fun k => (hnn k).2.2.2
  have hQ := (mbiQ_skipFree_QMatrix P hP).2.1
  have hfin : ∀ t (a b : ℤ), transition (Set.Ici 0) (mbiQ P) t a b ≠ ⊤ := fun t a b =>
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((ENNReal.le_tsum b).trans (transition_tsum_le_one _ _ hQ t a))
  set h : ℝ → ℝ≥0∞ := fun t => ∑' y : ℕ,
    transition (Set.Ici 0) (mbiQ P) t x y * ENNReal.ofReal (s ^ y) with hh
  set f : ℝ → ℝ := fun v => Lam P v - Lam P s with hf
  have hpis : 0 ≤ ∑' k, piSeq P k * s ^ k := tsum_nonneg fun k => mul_nonneg (hpi k) (pow_nonneg hs.1 _)
  have hmono := Lam_strictMonoOn P hP
  -- step 1: exchange sum and integral
  have h1 : ∑' y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y * ENNReal.ofReal (s ^ y) =
      ∫⁻ t in Set.Ici 0, h t := by
    simp only [hh]; unfold SkipFreeFluct.MBI.resolvent
    rw [lintegral_tsum (fun y => ((measurable_transition _ _ _ _).mul_const _).aemeasurable)]
    congr 1; funext y
    rw [lintegral_mul_const _ (measurable_transition _ _ _ _)]
  -- step 2: the image of (s, s₀) under f is (0, ∞)
  have himg : f '' Set.Ioo s (s0 P) = Set.Ioi 0 := by
    ext w
    simp only [Set.mem_image, Set.mem_Ioi, hf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := hmono ⟨hs.1, hs.2⟩ ⟨by linarith [hs.1, hv.1], hv.2⟩ hv.1
      linarith
    · intro hw
      have hts : w + Lam P s ∈ Set.Ici (0 : ℝ) := by
        have := hbij.mapsTo ⟨hs.1, hs.2⟩; simp only [Set.mem_Ici] at this ⊢; linarith
      obtain ⟨v, hv, hLv⟩ := hbij.surjOn hts
      refine ⟨v, ⟨?_, hv.2⟩, by linarith⟩
      by_contra hle; push Not at hle
      have := hmono.monotoneOn hv ⟨hs.1, hs.2⟩ hle
      linarith
  have hderiv : ∀ v ∈ Set.Ioo s (s0 P), HasDerivWithinAt f (1 / psi P v) (Set.Ioo s (s0 P)) v :=
    fun v hv => ((Lam_hasDerivAt P hP v ⟨by linarith [hs.1, hv.1], hv.2⟩).sub_const _
      ).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioo s (s0 P)) := by
    intro a ha b hb hab
    simp only [hf] at hab
    exact hbij.injOn ⟨by linarith [hs.1, ha.1], ha.2⟩ ⟨by linarith [hs.1, hb.1], hb.2⟩
      (by linarith)
  rw [h1, setLIntegral_congr Ioi_ae_eq_Ici.symm, ← himg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj h,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hv' : v ∈ Set.Ico 0 (s0 P) := ⟨by linarith [hs.1, hv.1], hv.2⟩
  have hψ := psi_pos P hP v hv'
  have hfv : 0 ≤ f v := by
    have := hmono ⟨hs.1, hs.2⟩ hv' hv.1; simp only [hf]; linarith
  have hG := hgen x (f v) hfv s hs v hv' (by simp only [hf]; ring)
  have he : ∀ y : ℕ, transition (Set.Ici 0) (mbiQ P) (f v) x y * ENNReal.ofReal (s ^ y) =
      ENNReal.ofReal ((transition (Set.Ici 0) (mbiQ P) (f v) x y).toReal * s ^ y) := by
    intro y
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin _ _ _)]
  have hhv : h (f v) = ENNReal.ofReal (v ^ x * ((∑' k, piSeq P k * s ^ k) *
      ∑' k, varpi P k * v ^ k)) := by
    simp only [hh, he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => mul_nonneg ENNReal.toReal_nonneg
      (pow_nonneg hs.1 _)) hG.summable, hG.tsum_eq]
  rw [hhv, (hgf v hv').2.2.2.2.tsum_eq, abs_of_pos (one_div_pos.mpr hψ),
    ← ENNReal.ofReal_mul (one_div_pos.mpr hψ).le, ← ENNReal.ofReal_mul hpis]
  congr 1
  field_simp

/-- One-sided identity theorem for power series. -/
lemma coeff_zero_of_tsum_zero (c : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hsum : Summable (fun n => |c n| * r ^ n))
    (h0 : ∀ s ∈ Set.Ioo 0 r, ∑' n, c n * s ^ n = 0) : ∀ n, c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ k ih =>
    have hMs : Summable (fun n => |c (n + k + 1)| * r ^ n) := by
      have h1 := (summable_nat_add_iff (k + 1)).mpr hsum
      refine (h1.mul_left (1 / r ^ (k + 1))).congr fun n => ?_
      rw [show n + (k + 1) = n + k + 1 by omega, pow_add]
      field_simp
      ring
    set M := ∑' n, |c (n + k + 1)| * r ^ n with hM
    have hM0 : 0 ≤ M := tsum_nonneg fun n => by positivity
    have key : ∀ s ∈ Set.Ioo 0 r, |c k| ≤ s * M := by
      intro s hs
      have hsr : Summable (fun n => c n * s ^ n) := by
        refine Summable.of_norm_bounded hsum fun n => ?_
        rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_of_nonneg hs.1.le]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hs.2.le _) (abs_nonneg _)
      have e1 := hsr.sum_add_tsum_nat_add k
      have hz : ∑ i ∈ Finset.range k, c i * s ^ i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.1 hi), zero_mul]
      rw [hz, zero_add, h0 s hs] at e1
      have hsr' : Summable (fun n => c (n + k) * s ^ (n + k)) := (summable_nat_add_iff k).mpr hsr
      rw [hsr'.tsum_eq_zero_add] at e1
      simp only [zero_add] at e1
      have hb : ∀ n, |c (n + 1 + k) * s ^ (n + 1 + k)| ≤ s ^ (k + 1) * (|c (n + k + 1)| * r ^ n) := by
        intro n
        rw [abs_mul, abs_of_nonneg (pow_nonneg hs.1.le _), show n + 1 + k = n + k + 1 by omega]
        rw [show s ^ (n + k + 1) = s ^ (k + 1) * s ^ n by rw [← pow_add]; congr 1; omega]
        have := pow_le_pow_left₀ hs.1.le hs.2.le n
        have h3 : 0 ≤ s ^ (k + 1) := pow_nonneg hs.1.le _
        nlinarith [abs_nonneg (c (n + k + 1)), mul_le_mul_of_nonneg_left this
          (mul_nonneg (abs_nonneg (c (n + k + 1))) h3)]
      have hsumb : Summable (fun n => c (n + 1 + k) * s ^ (n + 1 + k)) :=
        Summable.of_norm_bounded (hMs.mul_left (s ^ (k + 1))) (fun n => by
          rw [Real.norm_eq_abs]; exact hb n)
      have hle : |∑' n, c (n + 1 + k) * s ^ (n + 1 + k)| ≤ s ^ (k + 1) * M := by
        rw [hM, ← tsum_mul_left]
        refine (norm_tsum_le_tsum_norm hsumb.norm).trans ?_
        exact Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hb n) hsumb.norm
          (hMs.mul_left _)
      have hck : |c k| * s ^ k ≤ s ^ k * (s * M) := by
        have : c k * s ^ k = -∑' n, c (n + 1 + k) * s ^ (n + 1 + k) := by linarith
        rw [← abs_of_nonneg (pow_nonneg hs.1.le k), ← abs_mul, this, abs_neg,
          abs_of_nonneg (pow_nonneg hs.1.le k)]
        calc _ ≤ s ^ (k + 1) * M := hle
          _ = s ^ k * (s * M) := by ring
      have hsk : 0 < s ^ k := pow_pos hs.1 k
      nlinarith
    by_contra hne
    have hpos : 0 < |c k| := abs_pos.mpr hne
    set s := min (r / 2) (|c k| / (2 * (M + 1))) with hs
    have hs1 : 0 < s := lt_min (by linarith) (by positivity)
    have hs2 : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h := key s ⟨hs1, hs2⟩
    have h3 : s ≤ |c k| / (2 * (M + 1)) := min_le_right _ _
    have h4 : s * M ≤ |c k| / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right h3 hM0
    have h5 : |c k| / (2 * (M + 1)) * M < |c k| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith


lemma coeff_zero_of_hasSum_zero (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (h : ∀ s ∈ Set.Ioo 0 R, HasSum (fun n => c n * s ^ n) 0) : ∀ n, c n = 0 := by
  have hs1 : 3 * R / 4 ∈ Set.Ioo 0 R := ⟨by positivity, by linarith⟩
  have ht := (h _ hs1).summable.tendsto_cofinite_zero
  have hev : ∀ᶠ n in cofinite, ‖|c n| * (R / 2) ^ n‖ ≤ (2 / 3 : ℝ) ^ n := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 one_pos)] with n hn
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 * R / 4) ^ n)]
      at hn
    rw [Real.norm_of_nonneg (by positivity)]
    have e : (R / 2) ^ n = (3 * R / 4) ^ n * (2 / 3) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [e, ← mul_assoc]
    exact mul_le_of_le_one_left (by positivity) hn.le
  have hsum : Summable (fun n => |c n| * (R / 2) ^ n) :=
    Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      hev
  exact coeff_zero_of_tsum_zero c (R / 2) (by positivity) hsum
    (fun s hs => (h s ⟨hs.1, by linarith [hs.2]⟩).tsum_eq)

lemma ratio_continuousOn (P : MBIParams) (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    ContinuousOn (fun u => phiImm P u / psi P u) (Set.Icc 0 s) := by
  obtain ⟨hnn, hgf⟩ := lemma_5_1 P hP
  have hk : ∀ k, 0 ≤ kappa P k := fun k => (hnn k).2.2.1
  have hmem : ∀ v ∈ Set.Icc 0 s, v ∈ Set.Ico 0 (s0 P) := fun v hv => ⟨hv.1, hv.2.trans_lt hs.2⟩
  have hser : ContinuousOn (fun u => ∑' k, kappa P k * u ^ k) (Set.Icc 0 s) := by
    refine continuousOn_tsum (u := fun k => kappa P k * s ^ k) (fun k => by fun_prop)
      (hgf s hs).2.2.1.summable (fun k u hu => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hk k), norm_pow, Real.norm_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1 hu.2 _) (hk k)
  refine hser.congr fun u hu => ?_
  exact ((hgf u (hmem u hu)).2.2.1.tsum_eq).symm


theorem transient_part (P : MBIParams) (hP : P.Valid) :
    AllTransient (Set.Ici 0) (mbiQ P) → ∀ x y : ℕ,
      IntI P x ≠ ⊤ ∧ resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ ∧
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal = piSeq P y * (IntI P x).toReal - calH P y x := by
  intro hT
  obtain ⟨hnn, hgf⟩ := lemma_5_1 P hP
  have hpi : ∀ k, 0 ≤ piSeq P k := fun k => (hnn k).2.2.2
  have hs0 := s0_pos P hP
  have hs1 := s0_le_one P hP
  have h0mem : (0 : ℝ) ∈ Set.Ico 0 (s0 P) := ⟨le_rfl, hs0⟩
  have hpis0 : ∑' k, piSeq P k * (0 : ℝ) ^ k = 1 := by
    rw [(hgf 0 h0mem).2.2.2.1.tsum_eq]; simp
  set K : ℕ → ℝ → ℝ := fun x v => v ^ x / psi P v *
    Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u) with hK
  have hIntI : ∀ x, IntI P x = ∫⁻ v in Set.Ioo 0 (s0 P), ENNReal.ofReal (K x v) := fun x => rfl
  -- G(x, 0) = I(x)
  have hG0 : ∀ x : ℕ, resolvent (Set.Ici 0) (mbiQ P) x 0 = IntI P x := by
    intro x
    have h := gf_resolvent P hP x 0 h0mem
    rw [hpis0, ENNReal.ofReal_one, one_mul, tsum_eq_single 0 (fun y hy => by
      simp [zero_pow hy])] at h
    simp only [pow_zero, ENNReal.ofReal_one, mul_one, Nat.cast_zero] at h
    rw [h]; rfl
  -- I(x) ≤ I(0) = G(0, 0) < ∞
  have hIfin : ∀ x, IntI P x ≠ ⊤ := by
    intro x
    have hle : IntI P x ≤ IntI P 0 := by
      rw [hIntI, hIntI]
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
        (Eventually.of_forall fun v hv => ENNReal.ofReal_le_ofReal ?_))
      have hψ := psi_pos P hP v ⟨hv.1.le, hv.2⟩
      simp only [hK, pow_zero]
      have : v ^ x ≤ 1 := pow_le_one₀ hv.1.le (by linarith [hv.2])
      have h2 : 0 ≤ 1 / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u) := by
        positivity
      calc v ^ x / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u)
          = v ^ x * (1 / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u)) := by
            ring
        _ ≤ 1 * (1 / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u)) :=
            mul_le_mul_of_nonneg_right this h2
        _ = 1 / psi P v * Real.exp (-∫ u in (0 : ℝ)..v, phiImm P u / psi P u) := one_mul _
    have h00 := hG0 0
    have hT0 := hT 0 (by simp)
    refine ne_top_of_le_ne_top ?_ hle
    rw [← h00]; exact_mod_cast hT0.ne
  intro x
  set I := IntI P x with hIdef
  have hI := hIfin x
  set J : ℝ → ℝ≥0∞ := fun s => ∫⁻ v in Set.Ioo s (s0 P), ENNReal.ofReal (K x v) with hJ
  have hJle : ∀ s ∈ Set.Ico 0 (s0 P), J s ≤ I := fun s hs =>
    lintegral_mono_set (Set.Ioo_subset_Ioo_left hs.1)
  have hJfin : ∀ s ∈ Set.Ico 0 (s0 P), J s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hI (hJle s hs)
  have hpisn : ∀ s ∈ Set.Ico 0 (s0 P), 0 ≤ ∑' k, piSeq P k * s ^ k := fun s hs =>
    tsum_nonneg fun k => mul_nonneg (hpi k) (pow_nonneg hs.1 _)
  have hgfR : ∀ s ∈ Set.Ico 0 (s0 P), ∑' y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y *
      ENNReal.ofReal (s ^ y) = ENNReal.ofReal (∑' k, piSeq P k * s ^ k) * J s :=
    fun s hs => gf_resolvent P hP x s hs
  have hne : ∀ s ∈ Set.Ico 0 (s0 P), ∑' y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y *
      ENNReal.ofReal (s ^ y) ≠ ⊤ := fun s hs => by
    rw [hgfR s hs]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hJfin s hs)
  have hGfin : ∀ y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ := by
    intro y hy
    have hm : s0 P / 2 ∈ Set.Ico 0 (s0 P) := ⟨by positivity, by linarith⟩
    have h1 : resolvent (Set.Ici 0) (mbiQ P) x y * ENNReal.ofReal ((s0 P / 2) ^ y) ≤
        ∑' y : ℕ, resolvent (Set.Ici 0) (mbiQ P) x y * ENNReal.ofReal ((s0 P / 2) ^ y) :=
      ENNReal.le_tsum y
    rw [hy, ENNReal.top_mul (by simp [ENNReal.ofReal_eq_zero, not_le, pow_pos (half_pos hs0)])]
      at h1
    exact hne _ hm (top_le_iff.mp h1)
  -- real form of the generating function
  have hGreal : ∀ s ∈ Set.Ico 0 (s0 P), HasSum (fun y : ℕ =>
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal * s ^ y)
      ((∑' k, piSeq P k * s ^ k) * (J s).toReal) := by
    intro s hs
    have h2 := (ENNReal.summable_toReal (hne s hs)).hasSum
    rw [← ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (hGfin y) ENNReal.ofReal_ne_top),
      hgfR s hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hpisn s hs)] at h2
    have hterm : ∀ y : ℕ, (resolvent (Set.Ici 0) (mbiQ P) x y * ENNReal.ofReal (s ^ y)).toReal =
        (resolvent (Set.Ici 0) (mbiQ P) x y).toReal * s ^ y := by
      intro y; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.1 _)]
    simpa only [hterm] using h2
  -- continuity of the integrand on [0, s]
  have hKc : ∀ s ∈ Set.Ico 0 (s0 P), ContinuousOn (K x) (Set.Icc 0 s) := by
    intro s hs
    have hIv : ContinuousOn (fun v => ∫ u in (0 : ℝ)..v, phiImm P u / psi P u) (Set.Icc 0 s) := by
      have := intervalIntegral.continuousOn_primitive_interval'
        ((ratio_continuousOn P hP s hs).intervalIntegrable_of_Icc (μ := volume) hs.1)
        (Set.left_mem_uIcc (a := (0:ℝ)) (b := s))
      rwa [Set.uIcc_of_le hs.1] at this
    have hψc : ContinuousOn (psi P) (Set.Icc 0 s) :=
      (psi_continuousOn P hP).mono (Set.Icc_subset_Icc le_rfl (by linarith [hs.2]))
    refine ((continuousOn_pow x).div hψc fun v hv => ?_).mul (hIv.neg.rexp)
    exact (psi_pos P hP v ⟨hv.1, lt_of_le_of_lt hv.2 hs.2⟩).ne'
  have hKnn : ∀ s ∈ Set.Ico 0 (s0 P), ∀ v ∈ Set.Icc 0 s, 0 ≤ K x v := by
    intro s hs v hv
    have := psi_pos P hP v ⟨hv.1, lt_of_le_of_lt hv.2 hs.2⟩
    simp only [hK]; have := pow_nonneg hv.1 x; positivity
  -- splitting I(x) at s
  have hsplit : ∀ s ∈ Set.Ioo 0 (s0 P),
      (J s).toReal = I.toReal - ∫ v in (0 : ℝ)..s, K x v := by
    intro s hs
    have hs' : s ∈ Set.Ico 0 (s0 P) := ⟨hs.1.le, hs.2⟩
    have hU : I = (∫⁻ v in Set.Ioc 0 s, ENNReal.ofReal (K x v)) + J s := by
      rw [hIdef, hIntI, ← Set.Ioc_union_Ioo_eq_Ioo hs.1.le hs.2]
      rw [lintegral_union measurableSet_Ioo (Set.disjoint_left.mpr
        fun v (h1 : v ∈ Set.Ioc 0 s) (h2 : v ∈ Set.Ioo s (s0 P)) => by linarith [h1.2, h2.1])]
    have hint : IntegrableOn (K x) (Set.Ioc 0 s) :=
      ((hKc s hs').integrableOn_Icc (μ := volume)).mono_set Set.Ioc_subset_Icc_self
    have hA : ∫⁻ v in Set.Ioc 0 s, ENNReal.ofReal (K x v) =
        ENNReal.ofReal (∫ v in (0 : ℝ)..s, K x v) := by
      rw [intervalIntegral.integral_of_le hs.1.le, ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv =>
          hKnn s hs' v ⟨hv.1.le, hv.2⟩))]
    have hAnn : 0 ≤ ∫ v in (0 : ℝ)..s, K x v :=
      intervalIntegral.integral_nonneg hs.1.le fun v hv => hKnn s hs' v hv
    have hU' : I = ENNReal.ofReal (∫ v in (0 : ℝ)..s, K x v) + J s := by
      rw [hU, hA]
    rw [hU', ENNReal.toReal_add ENNReal.ofReal_ne_top (hJfin s hs'),
      ENNReal.toReal_ofReal hAnn]
    ring
  -- the generating function of ℋ
  have hH : ∀ s ∈ Set.Ioo 0 (s0 P), HasSum (fun y : ℕ => calH P y x * s ^ y)
      ((∑' k, piSeq P k * s ^ k) * ∫ v in (0 : ℝ)..s, K x v) := by
    intro s hs
    have hs' : s ∈ Set.Ico 0 (s0 P) := ⟨hs.1.le, hs.2⟩
    convert theorem_5_4_gf P hP x s hs' using 1
    have hII : ∀ v ∈ Set.Icc 0 s, IntervalIntegrable (fun u => phiImm P u / psi P u) volume 0 v :=
      fun v hv => ((ratio_continuousOn P hP s hs').mono (Set.Icc_subset_Icc le_rfl hv.2)
        ).intervalIntegrable_of_Icc hv.1
    rw [(hgf s hs').2.2.2.1.tsum_eq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hs.1.le] at hv
    simp only [hK]
    rw [← intervalIntegral.integral_interval_sub_left (hII s ⟨hs.1.le, le_rfl⟩) (hII v hv),
      Real.exp_sub, Real.exp_neg]
    ring
  -- identify coefficients
  have hc := coeff_zero_of_hasSum_zero (fun y => (resolvent (Set.Ici 0) (mbiQ P) x y).toReal -
      piSeq P y * I.toReal + calH P y x) (s0 P) hs0 (fun s hs => by
    have hs' : s ∈ Set.Ico 0 (s0 P) := ⟨hs.1.le, hs.2⟩
    have h3 := ((hGreal s hs').sub (((hgf s hs').2.2.2.1).mul_right I.toReal)).add (hH s hs)
    rw [hsplit s hs, (hgf s hs').2.2.2.1.tsum_eq] at h3
    have hv : Real.exp (∫ u in (0 : ℝ)..s, phiImm P u / psi P u) *
          (I.toReal - ∫ v in (0 : ℝ)..s, K x v) -
        Real.exp (∫ u in (0 : ℝ)..s, phiImm P u / psi P u) * I.toReal +
        Real.exp (∫ u in (0 : ℝ)..s, phiImm P u / psi P u) * ∫ v in (0 : ℝ)..s, K x v = 0 := by
      ring
    rw [hv] at h3
    have e : (fun (y : ℕ) => ((resolvent (Set.Ici 0) (mbiQ P) x y).toReal - piSeq P y * I.toReal +
        calH P y x) * s ^ y) = fun (y : ℕ) => (resolvent (Set.Ici 0) (mbiQ P) x y).toReal * s ^ y -
        piSeq P y * s ^ y * I.toReal + calH P y x * s ^ y := funext fun y => by ring
    rw [e]; exact h3)
  intro y
  refine ⟨hI, hGfin y, ?_⟩
  have := hc y
  linarith

end MBI541

open SkipFreeFluct.MBI MBI541 in
theorem solution (P : MBIParams) (hP : P.Valid) :
    (AllTransient (Set.Ici 0) (mbiQ P) → ∀ x y : ℕ,
      IntI P x ≠ ⊤ ∧ resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ ∧
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal = piSeq P y * (IntI P x).toReal - calH P y x) ∧
    (IsMBP P → ∀ x y : ℕ, 1 ≤ y →
      resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ ∧
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal =
        1 / y * (s0 P ^ x * W P (y - 1) - Wz P ((y : ℤ) - x - 1))) :=
  ⟨transient_part P hP, theorem_5_4_1_mbp P hP⟩
