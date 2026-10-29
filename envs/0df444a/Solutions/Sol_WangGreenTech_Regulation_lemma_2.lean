-- Prove2me | solution 1 for WangGreenTech.Regulation.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:33:32.423192+00:00
-- url     : https://prove2.me/submissions/77236ab3-af28-4a2a-8b55-7743227144e0

import Mathlib
import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

open WangGreenTech.Regulation MeasureTheory Set

noncomputable def s226w_Q (v : ℝ) : ℝ :=
  ((max 0 (v+1))^2 - 2*(max 0 v)^2 + (max 0 (v-1))^2)/2

lemma s226w_Qcase (v : ℝ) : (v ≤ -1 ∧ s226w_Q v = 0) ∨ (-1 ≤ v ∧ v ≤ 0 ∧ s226w_Q v = (v+1)^2/2) ∨
    (0 ≤ v ∧ v ≤ 1 ∧ s226w_Q v = 1 - (1-v)^2/2) ∨ (1 ≤ v ∧ s226w_Q v = 1) := by
  unfold s226w_Q
  rcases le_total v (-1) with h1 | h1
  · left; refine ⟨h1, ?_⟩
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  rcases le_total v 0 with h2 | h2
  · right; left; refine ⟨h1, h2, ?_⟩
    rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  rcases le_total v 1 with h3 | h3
  · right; right; left; refine ⟨h2, h3, ?_⟩
    rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · right; right; right; refine ⟨h3, ?_⟩
    rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring

lemma s226w_Qlip {x y : ℝ} (h : x ≤ y) :
    0 ≤ s226w_Q y - s226w_Q x ∧ s226w_Q y - s226w_Q x ≤ y - x := by
  rcases s226w_Qcase x with ⟨a1, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, e1⟩ <;>
  rcases s226w_Qcase y with ⟨b1, f1⟩ | ⟨b1, b2, f1⟩ | ⟨b1, b2, f1⟩ | ⟨b1, f1⟩ <;>
  rw [e1, f1] <;> constructor <;> nlinarith

lemma s226w_Q0 {v : ℝ} (h : v ≤ -1) : s226w_Q v = 0 := by
  rcases s226w_Qcase v with ⟨a1, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, e1⟩
  · exact e1
  · rw [e1]; have : v = -1 := by linarith
    subst this; norm_num
  · linarith
  · linarith

lemma s226w_Q1 {v : ℝ} (h : 1 ≤ v) : s226w_Q v = 1 := by
  rcases s226w_Qcase v with ⟨a1, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, e1⟩
  · linarith
  · linarith
  · rw [e1]; have : v = 1 := by linarith
    subst this; norm_num
  · exact e1

lemma s226w_Qcont : Continuous s226w_Q := by
  unfold s226w_Q; fun_prop

lemma s226w_F1 {e b v : ℝ} (he : 0 < e) (hb0 : 0 ≤ b) (hb : b ≤ 2*e) (hv : v < 0) :
    2*e*v + b/2 - b * s226w_Q v < 0 := by
  rcases s226w_Qcase v with ⟨a1, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, e1⟩ <;> rw [e1]
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hb) (show 0 ≤ -(v + v^2/2) by nlinarith),
      mul_pos he (mul_pos (neg_pos.2 hv) (neg_pos.2 hv))]
  · linarith
  · linarith

lemma s226w_F2 {e b v : ℝ} (he : 0 < e) (hb0 : 0 ≤ b) (hb : b ≤ 2*e) (hv : 0 ≤ v) :
    0 ≤ 2*e*v + b/2 - b * s226w_Q v := by
  rcases s226w_Qcase v with ⟨a1, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, a2, e1⟩ | ⟨a1, e1⟩ <;> rw [e1]
  · linarith
  · have : v = 0 := by linarith
    subst this; nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.2 hb) hv, mul_nonneg hb0 (sq_nonneg v)]
  · nlinarith [mul_le_mul_of_nonneg_left a1 he.le]

lemma s226w_int (p : Model) (hε : 0 < p.ε) (f : ℝ → ℝ) (x : ℝ) :
    ∫ θ, f θ ∂posterior p x = (2*p.ε)⁻¹ * ∫ θ in (x-p.ε)..(x+p.ε), f θ := by
  unfold posterior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]

lemma s226w_intg (p : Model) (hε : 0 < p.ε) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Integrable f (posterior p x) := by
  unfold posterior
  exact (hf.integrableOn_Icc).smul_measure
    (ENNReal.inv_ne_top.2 (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.2 (by linarith)))

lemma s226w_b1 {a c : ℝ} (h : a ≤ c) (hc : c ≤ 0) : ∫ s in a..c, max 0 s = 0 := by
  have : ∫ s in a..c, max 0 s = ∫ s in a..c, (0:ℝ) :=
    intervalIntegral.integral_congr (fun s hs => by
      rw [uIcc_of_le h] at hs; exact max_eq_left (hs.2.trans hc))
  rw [this]; simp

lemma s226w_b2 {a c : ℝ} (h : a ≤ c) (ha : 0 ≤ a) : ∫ s in a..c, max 0 s = (c^2 - a^2)/2 := by
  have : ∫ s in a..c, max 0 s = ∫ s in a..c, s :=
    intervalIntegral.integral_congr (fun s hs => by
      rw [uIcc_of_le h] at hs; exact max_eq_right (ha.trans hs.1))
  rw [this]; exact integral_id

lemma s226w_base {a c : ℝ} (h : a ≤ c) :
    ∫ s in a..c, max 0 s = ((max 0 c)^2 - (max 0 a)^2)/2 := by
  rcases le_total c 0 with hc | hc
  · rw [s226w_b1 h hc, max_eq_left hc, max_eq_left (h.trans hc)]; ring
  rcases le_total 0 a with ha | ha
  · rw [s226w_b2 h ha, max_eq_right hc, max_eq_right ha]
  · have hi : ∀ u v : ℝ, IntervalIntegrable (fun s : ℝ => max 0 s) volume u v :=
      fun u v => (continuous_const.max continuous_id).intervalIntegrable u v
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi a 0) (hi 0 c),
      s226w_b1 ha le_rfl, s226w_b2 hc le_rfl, max_eq_right hc, max_eq_left ha]; ring

lemma s226w_shift {a c k : ℝ} (h : a ≤ c) :
    ∫ s in a..c, max 0 (s - k) = ((max 0 (c-k))^2 - (max 0 (a-k))^2)/2 := by
  have := intervalIntegral.integral_comp_sub_right (a := a) (b := c) (fun s : ℝ => max 0 s) k
  rw [this, s226w_base (by linarith)]

lemma s226w_tm (p : Model) (hε : 0 < p.ε) (t θ : ℝ) :
    thresholdMass p t θ = (max 0 (θ - (t - p.ε)) - max 0 (θ - (t + p.ε)))/(2*p.ε) := by
  unfold thresholdMass
  rcases le_total (θ - (t - p.ε)) 0 with h1 | h1
  · have : (θ + p.ε - t)/(2*p.ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [max_eq_left this, min_eq_right zero_le_one, max_eq_left h1, max_eq_left (by linarith)]
    simp
  rcases le_total (θ - (t + p.ε)) 0 with h2 | h2
  · have h3 : 0 ≤ (θ + p.ε - t)/(2*p.ε) := div_nonneg (by linarith) (by linarith)
    have h4 : (θ + p.ε - t)/(2*p.ε) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [max_eq_right h3, min_eq_right h4, max_eq_right h1, max_eq_left h2]; congr 1; ring
  · have h4 : 1 ≤ (θ + p.ε - t)/(2*p.ε) := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [max_eq_right (by linarith), min_eq_left h4, max_eq_right h1, max_eq_right h2,
      eq_div_iff (by linarith)]; ring

lemma s226w_tmc (p : Model) (t : ℝ) : Continuous (thresholdMass p t) := by
  show Continuous (fun θ => min 1 (max 0 ((θ + p.ε - t) / (2 * p.ε)))); fun_prop

lemma s226w_mm {e y : ℝ} (he : 0 ≤ e) : max 0 (e*y) = e * max 0 y := by
  rw [mul_max_of_nonneg _ _ he, mul_zero]

lemma s226w_alpha (p : Model) (hε : 0 < p.ε) (t x : ℝ) :
    ∫ θ in (x-p.ε)..(x+p.ε), thresholdMass p t θ = 2*p.ε * s226w_Q ((x-t)/(2*p.ε)) := by
  simp_rw [s226w_tm p hε t]
  have ii : ∀ k : ℝ, IntervalIntegrable (fun θ : ℝ => max 0 (θ - k)) volume (x-p.ε) (x+p.ε) :=
    fun k => (by fun_prop : Continuous (fun θ : ℝ => max 0 (θ - k))).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (ii _) (ii _),
    s226w_shift (by linarith), s226w_shift (by linarith)]
  unfold s226w_Q
  set v := (x-t)/(2*p.ε) with hvdef
  have hv : 2*p.ε*v = x - t := by rw [hvdef]; field_simp
  have e1 : x + p.ε - (t - p.ε) = 2*p.ε*(v+1) := by rw [mul_add, hv]; ring
  have e2 : x - p.ε - (t - p.ε) = 2*p.ε*v := by rw [hv]; ring
  have e3 : x + p.ε - (t + p.ε) = 2*p.ε*v := by rw [hv]; ring
  have e4 : x - p.ε - (t + p.ε) = 2*p.ε*(v-1) := by rw [mul_sub, hv]; ring
  have h2 : (0:ℝ) ≤ 2*p.ε := by linarith
  rw [e1, e2, e3, e4, s226w_mm h2, s226w_mm h2, s226w_mm h2]
  field_simp; ring

lemma s226w_lin (p : Model) (hε : 0 < p.ε) (K B t x : ℝ) :
    ∫ θ, (K + θ - B * thresholdMass p t θ) ∂posterior p x =
      K + x - B * s226w_Q ((x-t)/(2*p.ε)) := by
  have hc := s226w_tmc p t
  rw [s226w_int p hε, intervalIntegral.integral_sub ((by fun_prop : Continuous (fun θ : ℝ => K + θ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun θ => B * thresholdMass p t θ)).intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun _ : ℝ => K) (g := fun x : ℝ => x)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, s226w_alpha p hε, intervalIntegral.integral_const, integral_id,
    smul_eq_mul]
  field_simp; ring

lemma s226w_mass (p : Model) (hε : 0 < p.ε) (t θ : ℝ) :
    adoptionMass p (thresholdProfile t) θ = thresholdMass p t θ := by
  have hin : ∫ x, (if t ≤ x then (1:ℝ) else 0) ∂signalLaw p θ = thresholdMass p t θ := by
    rw [show (fun x : ℝ => if t ≤ x then (1:ℝ) else 0) = (Ici t).indicator 1 from by
      ext x; simp [indicator]]
    rw [integral_indicator_one measurableSet_Ici, Measure.real]
    unfold signalLaw posterior
    have hI : Ici t ∩ Icc (θ - p.ε) (θ + p.ε) = Icc (max t (θ - p.ε)) (θ + p.ε) := by
      ext z; simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]; tauto
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, hI, Real.volume_Icc,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal', s226w_tm p hε, div_eq_inv_mul]
    congr 1
    rcases le_total t (θ - p.ε) with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_right (by linarith)]; ring
    rcases le_total t (θ + p.ε) with h2 | h2
    · rw [max_eq_left h1, max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_left (by linarith)]; ring
  unfold adoptionMass thresholdProfile
  simp only [decide_eq_true_eq, hin]
  simp

theorem solution (p : Model) (hp : p.Valid) (qhat : ℝ)
    (hq0 : 0 < qhat) (hq1 : qhat < 1) (hb : p.b ≤ 2 * p.ε) :
    AdoptionEquilibrium p (fun _ => qhat) (thresholdProfile (fixedAdoptionCutoff p qhat)) ∧
    (∀ θ, adoptionMass p (thresholdProfile (fixedAdoptionCutoff p qhat)) θ =
      thresholdMass p (fixedAdoptionCutoff p qhat) θ) ∧
    (∀ i ∈ Ico (0 : ℝ) 1, ∀ x,
      thresholdProfile (fixedAdoptionCutoff p qhat) i x = true ↔ fixedAdoptionCutoff p qhat ≤ x) ∧
    (∀ lam : ℝ, 0 ≤ lam →
      (fixedDevelopmentSet p qhat lam).Nonempty ∧ BddBelow (fixedDevelopmentSet p qhat lam) ∧
      fixedDevelopmentSet p qhat lam = Ici (fixedDevelopmentCutoff p qhat lam) ∧
      SpecifiedBeliefEquilibrium p (fun _ => qhat) lam
        (thresholdProfile (fixedAdoptionCutoff p qhat)) (fixedDecision p qhat lam)) := by
  obtain ⟨hε, hb0, -, -, -, -, -, -, -, -⟩ := hp
  set t := fixedAdoptionCutoff p qhat with ht
  have hmass : ∀ θ, adoptionMass p (thresholdProfile t) θ = thresholdMass p t θ :=
    s226w_mass p hε t
  have htc := s226w_tmc p t
  have hFT : ∀ x, followerInterim p (fun _ => qhat) (thresholdProfile t) x true =
      (-p.fL + qhat*p.mH + (1-qhat)*p.mL) + x - p.b * s226w_Q ((x-t)/(2*p.ε)) := by
    intro x; unfold followerInterim expectation; simp only [hmass]
    rw [← s226w_lin p hε]; congr 1; ext θ; simp [followerPayoff]; ring
  have hFF : ∀ x, followerInterim p (fun _ => qhat) (thresholdProfile t) x false =
      qhat*(p.mH - p.fH) := by
    intro x; unfold followerInterim expectation
    rw [s226w_int p hε]; simp only [followerPayoff, Bool.false_eq_true, if_false]
    rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
  have hD : ∀ x, followerInterim p (fun _ => qhat) (thresholdProfile t) x true -
      followerInterim p (fun _ => qhat) (thresholdProfile t) x false =
      2*p.ε*((x-t)/(2*p.ε)) + p.b/2 - p.b * s226w_Q ((x-t)/(2*p.ε)) := by
    intro x; rw [hFT, hFF]
    have : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    rw [this, ht]; unfold fixedAdoptionCutoff; ring
  have hpos : ∀ x, t ≤ x → 0 ≤ 2*p.ε*((x-t)/(2*p.ε)) + p.b/2 - p.b * s226w_Q ((x-t)/(2*p.ε)) :=
    fun x hx => s226w_F2 hε hb0 hb (div_nonneg (by linarith) (by linarith))
  have hneg : ∀ x, x < t → 2*p.ε*((x-t)/(2*p.ε)) + p.b/2 - p.b * s226w_Q ((x-t)/(2*p.ε)) < 0 :=
    fun x hx => s226w_F1 hε hb0 hb (div_neg_of_neg_of_pos (by linarith) (by linarith))
  have hAE : AdoptionEquilibrium p (fun _ => qhat) (thresholdProfile t) := by
    refine ⟨?_, ?_, ?_⟩
    · unfold Profile.Measurable thresholdProfile
      apply measurable_to_bool
      have : ((fun z : ℝ × ℝ => decide (t ≤ z.2)) ⁻¹' {true}) = {z | t ≤ z.2} := by
        ext z; simp
      rw [this]; exact measurableSet_le measurable_const measurable_snd
    · intro x a; simp only [hmass]; apply s226w_intg p hε
      cases a <;> simp only [followerPayoff, Bool.false_eq_true, if_false, if_true] <;> fun_prop
    · intro i _ x
      have hσ : thresholdProfile t i x = decide (t ≤ x) := rfl
      rw [hσ]
      by_cases hx : t ≤ x
      · simp only [hx, decide_true]
        refine ⟨fun a => ?_, ?_⟩
        · cases a
          · linarith [hD x, hpos x hx]
          · exact le_rfl
        · simp
      · simp only [hx, decide_false]
        push_neg at hx
        refine ⟨fun a => ?_, fun h => ?_⟩
        · cases a
          · exact le_rfl
          · linarith [hD x, hneg x hx]
        · exfalso; linarith [hD x, hneg x hx]
  have hU : ∀ lam x, fixedUtility p qhat lam x =
      (lam - p.f₁ + qhat*p.mH + (1-qhat)*p.mL) + x - p.b * s226w_Q ((x-t)/(2*p.ε)) := by
    intro lam x; unfold fixedUtility expectation
    rw [← s226w_lin p hε]; congr 1; ext θ; simp [leaderPayoff]; ring
  have hUmono : ∀ lam, Monotone (fixedUtility p qhat lam) := by
    intro lam x y hxy
    rw [hU, hU]
    have hv : (x-t)/(2*p.ε) ≤ (y-t)/(2*p.ε) := div_le_div_of_nonneg_right (by linarith) (by linarith)
    obtain ⟨h1, h2⟩ := s226w_Qlip hv
    have hx : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    have hy : 2*p.ε*((y-t)/(2*p.ε)) = y - t := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2*p.ε),
      mul_le_mul_of_nonneg_right hb h1]
  have hUc : ∀ lam, Continuous (fixedUtility p qhat lam) := by
    intro lam
    rw [show fixedUtility p qhat lam = fun x =>
      (lam - p.f₁ + qhat*p.mH + (1-qhat)*p.mL) + x - p.b * s226w_Q ((x-t)/(2*p.ε)) from
      funext (hU lam)]
    have := s226w_Qcont
    fun_prop
  refine ⟨hAE, hmass, fun i _ x => by simp [thresholdProfile], fun lam hlam => ?_⟩
  set K := lam - p.f₁ + qhat*p.mH + (1-qhat)*p.mL with hK
  have hne : (fixedDevelopmentSet p qhat lam).Nonempty := by
    refine ⟨max (t + 2*p.ε) (p.b - K), ?_⟩
    show 0 ≤ fixedUtility p qhat lam _
    rw [hU, s226w_Q1]
    · linarith [le_max_right (t + 2*p.ε) (p.b - K)]
    · rw [le_div_iff₀ (by linarith)]; linarith [le_max_left (t + 2*p.ε) (p.b - K)]
  have hbdd : BddBelow (fixedDevelopmentSet p qhat lam) := by
    refine ⟨min (t - 2*p.ε) (-K), fun x hx => ?_⟩
    have hx' : 0 ≤ fixedUtility p qhat lam x := hx
    by_contra hc; push_neg at hc
    rw [hU, s226w_Q0] at hx'
    · linarith [min_le_right (t - 2*p.ε) (-K)]
    · rw [div_le_iff₀ (by linarith)]; linarith [min_le_left (t - 2*p.ε) (-K)]
  have hcl : IsClosed (fixedDevelopmentSet p qhat lam) := isClosed_le continuous_const (hUc lam)
  have hEq : fixedDevelopmentSet p qhat lam = Ici (fixedDevelopmentCutoff p qhat lam) := by
    ext y; constructor
    · intro hy; exact csInf_le hbdd hy
    · intro hy
      have hm : 0 ≤ fixedUtility p qhat lam (fixedDevelopmentCutoff p qhat lam) :=
        hcl.csInf_mem hne hbdd
      exact le_trans hm (hUmono lam hy)
  refine ⟨hne, hbdd, hEq, hAE, ?_, ?_, ?_⟩
  · unfold fixedDecision
    apply measurable_to_bool
    have : ((fun x => decide (0 ≤ fixedUtility p qhat lam x)) ⁻¹' {true}) =
        {x | 0 ≤ fixedUtility p qhat lam x} := by ext z; simp
    rw [this]; exact measurableSet_le measurable_const (hUc lam).measurable
  · intro x a; simp only [hmass]; apply s226w_intg p hε
    cases a <;> simp only [leaderPayoff, Bool.false_eq_true, if_false, if_true] <;> fun_prop
  · intro x
    have hT : expectation p x (fun θ => leaderPayoff p (fun _ => qhat) lam true θ
        (adoptionMass p (thresholdProfile t) θ)) = fixedUtility p qhat lam x := by
      simp only [hmass]; rfl
    have hF : expectation p x (fun θ => leaderPayoff p (fun _ => qhat) lam false θ
        (adoptionMass p (thresholdProfile t) θ)) = 0 := by
      simp [expectation, leaderPayoff]
    refine ⟨fun a => ?_, fun h0 => ?_⟩
    · by_cases hx : 0 ≤ fixedUtility p qhat lam x
      · have hd : fixedDecision p qhat lam x = true := by simp [fixedDecision, hx]
        rw [hd, hT]
        cases a
        · rw [hF]; exact hx
        · rw [hT]
      · have hd : fixedDecision p qhat lam x = false := by simp [fixedDecision, hx]
        rw [hd, hF]
        cases a
        · rw [hF]
        · rw [hT]; linarith
    · rw [hT] at h0
      simp [fixedDecision, h0]
