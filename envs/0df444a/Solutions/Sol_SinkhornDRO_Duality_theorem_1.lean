-- Prove2me | solution 1 for SinkhornDRO.Duality.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:17:57.799387+00:00
-- url     : https://prove2.me/submissions/c51dfa54-d14c-4742-9f06-233550e00902

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SinkhornDRO_Duality_SinkhornDistance
import Definitions.Def_SinkhornDRO_Duality_Dual

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DupacovaWets.Consistency (expect)
open SinkhornDRO.Duality

namespace SinkCE

/-- pointwise Gibbs inequality `p log (p/q) ≥ p - q`, strict unless `p = q`. -/
lemma gibbs_pt (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    p - q ≤ p * Real.log (p / q) ∧ (p * Real.log (p / q) ≤ p - q → p = q) := by
  rcases hp.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨by simp; linarith, fun h => ?_⟩
    simp at h; linarith
  · have hx : 0 < q / p := div_pos hq hpos
    have hlog : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv, inv_div]
    have key : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos hx
    have e1 : p * (q / p - 1) = q - p := by field_simp
    refine ⟨?_, fun h => ?_⟩
    · rw [hlog]; nlinarith [mul_le_mul_of_nonneg_left key hpos.le]
    · by_contra hne
      have hne' : q / p ≠ 1 := by
        intro h1; apply hne; field_simp at h1; linarith
      have key2 : Real.log (q / p) < q / p - 1 := Real.log_lt_sub_one_of_pos hx hne'
      rw [hlog] at h
      nlinarith [mul_lt_mul_of_pos_left key2 hpos]

lemma gibbs {ι : Type*} (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : HasSum p 1) (hqs : HasSum q 1)
    (hA : ∑' i, ENNReal.ofReal (p i * Real.log (p i / q i)) ≠ ⊤)
    (hle : ((∑' i, ENNReal.ofReal (p i * Real.log (p i / q i)) : ℝ≥0∞) : EReal) -
        ((∑' i, ENNReal.ofReal (-(p i * Real.log (p i / q i))) : ℝ≥0∞) : EReal) ≤ 0) :
    ∀ i, p i = q i := by
  set ℓ : ι → ℝ := fun i => p i * Real.log (p i / q i) with hℓ
  have hB : ∑' i, ENNReal.ofReal (-(ℓ i)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' i, ENNReal.ofReal (q i)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hq i).le) hqs.summable]
      exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
      have := (gibbs_pt (p i) (q i) (hp i) (hq i)).1
      have := hp i
      simp only [hℓ]; linarith
  have sA := ENNReal.summable_toReal hA
  have sB := ENNReal.summable_toReal hB
  simp only [ENNReal.toReal_ofReal'] at sA sB
  have eA := ENNReal.tsum_toReal_eq (f := fun i => ENNReal.ofReal (ℓ i)) (fun _ => ENNReal.ofReal_ne_top)
  have eB := ENNReal.tsum_toReal_eq (f := fun i => ENNReal.ofReal (-ℓ i)) (fun _ => ENNReal.ofReal_ne_top)
  simp only [ENNReal.toReal_ofReal'] at eA eB
  have hle' : (∑' i, max (ℓ i) 0) - ∑' i, max (-ℓ i) 0 ≤ 0 := by
    rw [← eA, ← eB]
    rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB] at hle
    rw [← EReal.coe_sub] at hle
    exact_mod_cast hle
  set t : ι → ℝ := fun i => (max (ℓ i) 0 - max (-ℓ i) 0) - p i + q i with ht
  have tpos : ∀ i, 0 ≤ t i := by
    intro i
    have h1 := (gibbs_pt (p i) (q i) (hp i) (hq i)).1
    have : max (ℓ i) 0 - max (-ℓ i) 0 = ℓ i := by
      rcases le_total 0 (ℓ i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    simp only [ht, this]; simp only [hℓ]; linarith
  have tsum_t : HasSum t ((∑' i, max (ℓ i) 0) - (∑' i, max (-ℓ i) 0) - 1 + 1) :=
    ((sA.hasSum.sub sB.hasSum).sub hps).add hqs
  have tle : ∀ i, t i ≤ 0 := by
    intro i
    have := tsum_t.summable.le_tsum i (fun j _ => tpos j)
    rw [tsum_t.tsum_eq] at this
    linarith
  intro i
  have h0 : t i = 0 := le_antisymm (tle i) (tpos i)
  have : max (ℓ i) 0 - max (-ℓ i) 0 = ℓ i := by
    rcases le_total 0 (ℓ i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  simp only [ht, this] at h0
  exact (gibbs_pt (p i) (q i) (hp i) (hq i)).2 (by simp only [hℓ] at h0 ⊢; linarith)

universe u

instance instDMS : DiscreteMeasurableSpace (ULift.{u} ℕ) :=
  ⟨fun s => measurableSet_preimage_up.mp MeasurableSet.of_discrete⟩

/-- the weights `q n = 2^{-(n+1)}` -/
noncomputable def q (n : ULift.{u} ℕ) : ℝ≥0∞ := 2⁻¹ ^ (n.down + 1)

noncomputable def nu : Measure (ULift.{u} ℕ) := Measure.sum fun n => q n • Measure.dirac n

lemma lintegral_nu (g : ULift.{u} ℕ → ℝ≥0∞) : ∫⁻ z, g z ∂nu = ∑' n, q n * g n := by
  simp [nu, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac]

lemma nu_singleton (b : ULift.{u} ℕ) : nu {b} = q b := by
  rw [nu, Measure.sum_apply _ (measurableSet_singleton b)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single b]
  · simp
  · intro n hn; simp [Measure.dirac_apply, hn]

lemma tsum_q : ∑' n : ULift.{u} ℕ, q n = 1 := by
  rw [← Equiv.ulift.symm.tsum_eq]
  simp only [q, Equiv.ulift_symm_down]
  simp only [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  rw [ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

instance nu_prob : IsProbabilityMeasure (nu.{u}) := by
  constructor
  rw [nu, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact tsum_q

lemma q_pos (n : ULift.{u} ℕ) : 0 < q n := by
  simp only [q]; exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _

lemma q_ne_top (n : ULift.{u} ℕ) : q n ≠ ⊤ := by
  simp [q]

def z0 : ULift.{u} ℕ := ⟨0⟩

section coupling
variable (γ : Measure (ULift.{u} ℕ × ULift.{u} ℕ))
  (hfst : γ.map Prod.fst = Measure.dirac z0)
include hfst

lemma off_zero (a b : ULift.{u} ℕ) (ha : a ≠ z0) : γ {(a, b)} = 0 := by
  refine measure_mono_null (t := Prod.fst ⁻¹' {a}) (by intro x hx; simp_all) ?_
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton a), hfst]
  simp [Measure.dirac_apply, ha]

lemma on_zero (b : ULift.{u} ℕ) : γ {(z0, b)} = (γ.map Prod.snd) {b} := by
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
  have hc : γ (Prod.fst ⁻¹' {z0})ᶜ = 0 := by
    rw [← Set.preimage_compl, ← Measure.map_apply measurable_fst
      (measurableSet_singleton z0).compl, hfst]
    simp [Measure.dirac_apply]
  rw [← measure_inter_conull (s := Prod.snd ⁻¹' {b}) hc]
  congr 1
  ext ⟨x, y⟩; simp [and_comm]

lemma lintegral_coupling (F : ULift.{u} ℕ × ULift.{u} ℕ → ℝ≥0∞) :
    ∫⁻ x, F x ∂γ = ∑' b, F (z0, b) * (γ.map Prod.snd) {b} := by
  rw [lintegral_countable', ENNReal.tsum_prod', tsum_eq_single z0]
  · simp_rw [on_zero γ hfst]
  · intro a ha
    simp [off_zero γ hfst a _ ha]

end coupling

lemma term_eq (x y : ℝ≥0∞) (hx : x ≠ ⊤) (hy0 : y ≠ 0) (hyt : y ≠ ⊤) :
    (ENNReal.log (x / y)).toENNReal * x =
        ENNReal.ofReal (x.toReal * Real.log (x.toReal / y.toReal)) ∧
      (-ENNReal.log (x / y)).toENNReal * x =
        ENNReal.ofReal (-(x.toReal * Real.log (x.toReal / y.toReal))) := by
  by_cases h0 : x = 0
  · subst h0; simp
  have h1 : x / y ≠ 0 := by simp [ENNReal.div_eq_zero_iff, h0, hyt]
  have h2 : x / y ≠ ⊤ := by simp [ENNReal.div_eq_top, hy0, hx]
  rw [ENNReal.log_pos_real h1 h2, ENNReal.toReal_div, ← EReal.coe_neg,
    EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
  refine ⟨?_, ?_⟩
  · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx, mul_comm]
  · rw [neg_mul_eq_mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx,
      mul_comm]

noncomputable def ell (P : Measure (ULift.{u} ℕ)) (b : ULift.{u} ℕ) : ℝ :=
  (P {b}).toReal * Real.log ((P {b}).toReal / (q b).toReal)

noncomputable def K (P : Measure (ULift.{u} ℕ)) : EReal :=
  if ∑' b, ENNReal.ofReal (ell P b) = ⊤ then ⊤
  else ((∑' b, ENNReal.ofReal (ell P b) : ℝ≥0∞) : EReal) -
    ((∑' b, ENNReal.ofReal (-ell P b) : ℝ≥0∞) : EReal)

lemma prod_singleton (b : ULift.{u} ℕ) :
    ((Measure.dirac z0).prod nu) {(z0, b)} = q b := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, nu_singleton]
  simp

lemma sinkhorn_ge (P : Measure (ULift.{u} ℕ)) [IsProbabilityMeasure P] :
    K P ≤ sinkhornDist (Measure.dirac z0) nu (fun _ _ => 0) 1 (Measure.dirac z0) P := by
  unfold sinkhornDist
  refine le_iInf₂ fun γ hγ => ?_
  split_ifs with h
  swap; · exact le_top
  have hac : γ ≪ (Measure.dirac z0).prod nu := h.resolve_left one_ne_zero
  obtain ⟨hprob, hfst, hsnd⟩ := hγ
  have hrn : ∀ b, γ.rnDeriv ((Measure.dirac z0).prod nu) (z0, b) = P {b} / q b := by
    intro b
    have := Measure.setLIntegral_rnDeriv hac {(z0, b)}
    rw [lintegral_singleton, prod_singleton, on_zero γ hfst, hsnd] at this
    rw [ENNReal.eq_div_iff (q_pos b).ne' (q_ne_top b), mul_comm, this]
  have hA : ∫⁻ p, ((((fun _ _ => (0 : ℝ≥0∞)) : ULift.{u} ℕ → ULift.{u} ℕ → ℝ≥0∞) p.1 p.2 : EReal) +
      ((1 : ℝ) : EReal) * ENNReal.log (γ.rnDeriv ((Measure.dirac z0).prod nu) p)).toENNReal ∂γ =
      ∑' b, ENNReal.ofReal (ell P b) := by
    rw [lintegral_coupling γ hfst, hsnd]
    congr 1; funext b
    simp only [EReal.coe_ennreal_zero, zero_add, EReal.coe_one, one_mul, hrn b]
    exact (term_eq _ _ (measure_ne_top P _) (q_pos b).ne' (q_ne_top b)).1
  have hB : ∫⁻ p, (-((((fun _ _ => (0 : ℝ≥0∞)) : ULift.{u} ℕ → ULift.{u} ℕ → ℝ≥0∞) p.1 p.2 : EReal) +
      ((1 : ℝ) : EReal) * ENNReal.log (γ.rnDeriv ((Measure.dirac z0).prod nu) p))).toENNReal ∂γ =
      ∑' b, ENNReal.ofReal (-ell P b) := by
    rw [lintegral_coupling γ hfst, hsnd]
    congr 1; funext b
    simp only [EReal.coe_ennreal_zero, zero_add, EReal.coe_one, one_mul, hrn b]
    exact (term_eq _ _ (measure_ne_top P _) (q_pos b).ne' (q_ne_top b)).2
  unfold expect
  rw [hA, hB]
  rfl

lemma feasible_eq (P : Measure (ULift.{u} ℕ)) [IsProbabilityMeasure P]
    (hP : sinkhornDist (Measure.dirac z0) nu (fun _ _ => 0) 1 (Measure.dirac z0) P ≤ ((0 : ℝ) : EReal)) :
    P = nu := by
  have hK := (sinkhorn_ge P).trans hP
  have hA : ∑' b, ENNReal.ofReal (ell P b) ≠ ⊤ := by
    intro h; rw [K, if_pos h] at hK; simp at hK
  rw [K, if_neg hA] at hK
  have hsum : ∀ (μ : Measure (ULift.{u} ℕ)), ∑' b, μ {b} = μ Set.univ := by
    intro μ
    have := Measure.tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ
    simpa using this
  have hps : HasSum (fun b => (P {b}).toReal) 1 := by
    have h1 := ENNReal.tsum_toReal_eq (f := fun b => P {b}) (fun b => measure_ne_top P _)
    rw [hsum, measure_univ] at h1
    have := (ENNReal.summable_toReal (f := fun b => P {b})
      (by rw [hsum, measure_univ]; exact ENNReal.one_ne_top)).hasSum
    rw [← h1] at this; simpa using this
  have hqs : HasSum (fun b => (q b).toReal) 1 := by
    have h1 := ENNReal.tsum_toReal_eq (f := fun b => q b) (fun b => q_ne_top b)
    rw [tsum_q] at h1
    have := (ENNReal.summable_toReal (f := fun b => q b)
      (by rw [tsum_q]; exact ENNReal.one_ne_top)).hasSum
    rw [← h1] at this; simpa using this
  have key := gibbs (fun b => (P {b}).toReal) (fun b => (q b).toReal)
    (fun b => ENNReal.toReal_nonneg) (fun b => ENNReal.toReal_pos (q_pos b).ne' (q_ne_top b))
    hps hqs hA (by simpa [ell] using hK)
  rw [Measure.ext_iff_singleton]
  intro b
  rw [nu_singleton]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (q_ne_top b)).mp (key b)

/-- the loss `f(n) = n²` -/
noncomputable def f (z : ULift.{u} ℕ) : EReal := (((z.down : ℝ) ^ 2 : ℝ) : EReal)

noncomputable abbrev c0 : ULift.{u} ℕ → ULift.{u} ℕ → ℝ≥0∞ := fun _ _ => 0

lemma kexp_c0 (x z : ULift.{u} ℕ) : kexp c0 1 x z = 1 := by
  simp [kexp]

lemma normalizer_c0 (x : ULift.{u} ℕ) : normalizer nu c0 1 x = 1 := by
  simp [normalizer, kexp_c0]

lemma Qker_c0 (x : ULift.{u} ℕ) : Qker nu c0 1 x = nu := by
  unfold Qker
  rw [normalizer_c0]
  have : (kexp c0 1 x) = 1 := by funext z; exact kexp_c0 x z
  rw [this, withDensity_one]; simp

lemma rhoBar_c0 : rhoBar (Measure.dirac z0) nu c0 1 0 = 0 := by
  simp [rhoBar, normalizer_c0]

lemma big_term (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ENNReal.ofReal (Real.exp ((lam * 1)⁻¹ * ((n : ℝ) ^ 2))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * lam + 1)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn' : (2 * lam + 1 : ℝ) ≤ n := le_trans hN.le (by exact_mod_cast hn)
  have h1 : ((n : ℝ) + 1) ≤ (lam * 1)⁻¹ * ((n : ℝ) ^ 2) := by
    rw [mul_one, inv_mul_eq_div, le_div_iff₀ hlam]
    nlinarith
  have h2 : (2 : ℝ) ^ (n + 1) ≤ Real.exp ((lam * 1)⁻¹ * ((n : ℝ) ^ 2)) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (2 : ℝ) ^ (n + 1) ≤ Real.exp 1 ^ (n + 1) := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp ((n : ℝ) + 1) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ _ := Real.exp_le_exp.mpr h1
  have h3 : (2 : ℝ≥0∞) ^ (n + 1) ≤ ENNReal.ofReal (Real.exp ((lam * 1)⁻¹ * ((n : ℝ) ^ 2))) := by
    have := ENNReal.ofReal_le_ofReal h2
    rwa [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat] at this
  calc (1 : ℝ≥0∞) = (2⁻¹ : ℝ≥0∞) ^ (n + 1) * 2 ^ (n + 1) := by
        rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
    _ ≤ _ := mul_le_mul_right h3 _

lemma dualInner_top (lam : ℝ) (hlam : 0 < lam) (x : ULift.{u} ℕ) :
    dualInner nu c0 1 f lam x = ⊤ := by
  unfold dualInner
  rw [Qker_c0, lintegral_nu]
  simp only [f, ← EReal.coe_mul, EReal.exp_coe]
  rw [← Equiv.ulift.symm.tsum_eq]
  simp only [q, Equiv.ulift_symm_down]
  by_contra hne
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
  have hev := ht.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (big_term lam hlam)).exists
  exact absurd hn1 (not_lt.mpr hn2)

lemma essSup_f : essSup f (nu.{u}) = ⊤ := by
  have hall : ∀ n : ULift.{u} ℕ, f n ≤ essSup f nu := by
    intro n
    have h := ae_le_essSup (μ := nu) (f := f)
    by_contra hn
    have : nu {n} = 0 :=
      measure_mono_null (fun z hz => by simp only [Set.mem_singleton_iff] at hz; subst hz; exact hn)
        (ae_iff.mp h)
    rw [nu_singleton] at this
    exact (q_pos n).ne' this
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨m, hm⟩ := exists_nat_gt y
  refine lt_of_lt_of_le ?_ (hall ⟨m⟩)
  simp only [f]
  rw [EReal.coe_lt_coe_iff]
  have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  linarith

lemma dualObj_top (lam : ℝ) (hlam : 0 ≤ lam) :
    dualObj (Measure.dirac z0) nu c0 1 0 f lam = ⊤ := by
  unfold dualObj
  split_ifs with h0
  · exact essSup_f
  have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h0)
  have he : expect (Measure.dirac z0) (fun x => ENNReal.log (dualInner nu c0 1 f lam x)) = ⊤ := by
    unfold expect
    simp [dualInner_top lam hpos]
  rw [he, rhoBar_c0, EReal.coe_mul_top_of_pos (by linarith), EReal.coe_add_top]

lemma dualValue_top : dualValue (Measure.dirac z0) nu c0 1 0 f = ⊤ := by
  unfold dualValue
  refine eq_top_iff.mpr (le_iInf₂ fun lam hlam => ?_)
  rw [dualObj_top lam hlam]

lemma expect_nu_f_lt : expect (nu.{u}) f < ⊤ := by
  have hA : ∫⁻ z, (f z).toENNReal ∂nu ≠ ⊤ := by
    rw [lintegral_nu]
    simp only [f, EReal.real_coe_toENNReal]
    rw [← Equiv.ulift.symm.tsum_eq]
    simp only [q, Equiv.ulift_symm_down]
    have hs : Summable (fun k : ℕ => (2⁻¹ : ℝ) * ((k : ℝ) ^ 2 * (2⁻¹ : ℝ) ^ k)) :=
      (summable_pow_mul_geometric_of_norm_lt_one 2 (r := (2⁻¹ : ℝ))
        (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)).mul_left _
    have heq : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal ((k : ℝ) ^ 2) =
        ENNReal.ofReal ((2⁻¹ : ℝ) * ((k : ℝ) ^ 2 * (2⁻¹ : ℝ) ^ k)) := by
      intro k
      rw [show (2⁻¹ : ℝ) * ((k : ℝ) ^ 2 * (2⁻¹ : ℝ) ^ k) = (2⁻¹ : ℝ) ^ (k + 1) * (k : ℝ) ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hB : ∫⁻ z, (-f z).toENNReal ∂nu = 0 := by
    have : (fun z => (-f z).toENNReal) = fun _ => 0 := by
      funext z
      apply EReal.toENNReal_of_nonpos
      simp only [f, ← EReal.coe_neg, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      nlinarith [sq_nonneg (z.down : ℝ)]
    rw [this, lintegral_zero]
  unfold expect
  rw [if_neg hA, hB]
  simp only [EReal.coe_ennreal_zero, sub_zero]
  exact lt_top_iff_ne_top.mpr (fun h => hA (EReal.coe_ennreal_eq_top_iff.mp h))

lemma primal_lt_top : primalValue (Measure.dirac z0) nu c0 1 0 f < ⊤ := by
  refine lt_of_le_of_lt ?_ expect_nu_f_lt
  unfold primalValue
  refine iSup₂_le fun P hP => ?_
  obtain ⟨hprob, hd⟩ := hP
  rw [feasible_eq P hd]

lemma regular (γ : Measure (ULift.{u} ℕ × ULift.{u} ℕ)) (hγ : IsProbabilityMeasure γ)
    (hfst : γ.map Prod.fst = Measure.dirac z0) :
    ∃ κ : Kernel (ULift.{u} ℕ) (ULift.{u} ℕ), IsMarkovKernel κ ∧ γ = Measure.dirac z0 ⊗ₘ κ := by
  have : IsProbabilityMeasure (γ.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  refine ⟨Kernel.const _ (γ.map Prod.snd), inferInstance, ?_⟩
  rw [Measure.compProd_const, Measure.ext_iff_singleton]
  rintro ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Set.singleton_prod_singleton]
  by_cases ha : a = z0
  · subst ha; rw [on_zero γ hfst]; simp
  · rw [off_zero γ hfst a b ha]; simp [ha]

lemma assumption1 : Assumption1 (Measure.dirac z0) (nu.{u}) c0 1 f where
  cost_measurable := measurable_const
  cost_finite := by simp
  normalizer_finite := by simp [normalizer_c0]
  loss_measurable := Measurable.of_discrete
  loss_ne_bot := fun z => EReal.coe_ne_bot _
  regular_conditional := regular

lemma hlog0 : Integrable (fun x => Real.log (normalizer (nu.{u}) c0 1 x).toReal)
    (Measure.dirac z0) := by
  simp [normalizer_c0]

end SinkCE

theorem solution : ¬ (∀ {Z : Type} [MeasurableSpace Z]
    (Phat ν : Measure Z) [IsProbabilityMeasure Phat] [SigmaFinite ν] (hν : ν ≠ 0)
    (c : Z → Z → ℝ≥0∞) (ε ρ : ℝ) (hε : 0 < ε) (f : Z → EReal)
    (hA : Assumption1 Phat ν c ε f)
    (hlog : Integrable (fun x => Real.log (normalizer ν c ε x).toReal) Phat),
    -- (I)
    ((∃ P : Measure Z, IsProbabilityMeasure P ∧ sinkhornDist Phat ν c ε Phat P ≤ (ρ : EReal)) ↔
        0 ≤ rhoBar Phat ν c ε ρ) ∧
    -- (II)
    (0 ≤ rhoBar Phat ν c ε ρ → primalValue Phat ν c ε ρ f = dualValue Phat ν c ε ρ f) ∧
    -- (III)
    (0 < rhoBar Phat ν c ε ρ →
      (Condition1Integrated Phat ν c ε f →
          primalValue Phat ν c ε ρ f = dualValue Phat ν c ε ρ f ∧ dualValue Phat ν c ε ρ f < ⊤) ∧
        (¬ Condition1Integrated Phat ν c ε f →
          primalValue Phat ν c ε ρ f = ⊤ ∧ dualValue Phat ν c ε ρ f = ⊤)) ∧
    -- (IV)
    (0 < rhoBar Phat ν c ε ρ → Condition1 Phat ν c ε f →
      ((IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) 0 ∧
          ∀ μ ∈ Set.Ici (0 : ℝ), IsMinOn (dualObj Phat ν c ε ρ f) (Set.Ici 0) μ → μ = 0) ↔
        (essSup f ν < ⊤ ∧
          (ε : EReal) * expect Phat (fun x => -ENNReal.log (Qker ν c ε x {z | f z = essSup f ν})) ≤
            (rhoBar Phat ν c ε ρ : EReal))))) := by
  intro H
  have h2 := (H (Measure.dirac SinkCE.z0) SinkCE.nu (IsProbabilityMeasure.ne_zero _) SinkCE.c0
    1 0 one_pos SinkCE.f SinkCE.assumption1 SinkCE.hlog0).2.1 (by rw [SinkCE.rhoBar_c0])
  rw [SinkCE.dualValue_top] at h2
  exact SinkCE.primal_lt_top.ne h2
