-- Prove2me | solution 1 for RoboAdvising.Sensitivity.proposition_5_1_ii_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:36:18.302206+00:00
-- url     : https://prove2.me/submissions/39ec4615-56d9-4a8e-b5cd-aead14d75ea6

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model
import Definitions.Def_RoboAdvising_Sensitivity_optimizer

set_option autoImplicit false

namespace RoboAdvisingP51

open RoboAdvising.Interaction

noncomputable def Qf (b φ : ℝ) : ℝ := Real.sqrt (1 + b * φ)

noncomputable def Ff (b p φ : ℝ) : ℝ := (1 + p / 2 * (φ - 1) * (Qf b φ - 1)) / Real.sqrt φ

noncomputable def Kf (b p φ : ℝ) : ℝ :=
  -1 / p + (Qf b φ - 1) * φ + (φ - 1) * (1 / 2 - 1 / (2 * Qf b φ))

noncomputable def bP (P : Params) : ℝ := P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)

lemma Qf_ge_one {b φ : ℝ} (hb : 0 ≤ b) (hφ : 0 ≤ φ) : 1 ≤ Qf b φ := by
  unfold Qf
  have h : (1:ℝ) ≤ 1 + b * φ := by nlinarith
  have := Real.sqrt_le_sqrt h
  simpa using this

lemma Qf_sq {b φ : ℝ} (hb : 0 ≤ b) (hφ : 0 ≤ φ) : Qf b φ ^ 2 = 1 + b * φ := by
  unfold Qf
  rw [Real.sq_sqrt (by positivity)]

lemma Qf_continuous (b : ℝ) : Continuous (Qf b) := by
  unfold Qf; fun_prop

lemma hasDerivAt_Qf {b φ : ℝ} (hb : 0 ≤ b) (hφ : 0 < φ) :
    HasDerivAt (Qf b) (b / (2 * Qf b φ)) φ := by
  have h1 : (0:ℝ) < 1 + b * φ := by positivity
  have := (((hasDerivAt_id φ).const_mul b).const_add 1).sqrt h1.ne'
  unfold Qf
  exact this.congr_deriv (by simp)

lemma hasDerivAt_Ff {b p φ : ℝ} (hb : 0 ≤ b) (hp : 0 < p) (hφ : 0 < φ) :
    HasDerivAt (Ff b p) (p * Kf b p φ / (2 * φ * Real.sqrt φ)) φ := by
  have hQ := hasDerivAt_Qf hb hφ
  have hN : HasDerivAt (fun x => 1 + p / 2 * (x - 1) * (Qf b x - 1))
      (p / 2 * ((Qf b φ - 1) + (φ - 1) * (b / (2 * Qf b φ)))) φ := by
    have h2 := (((hasDerivAt_id φ).sub_const 1).const_mul (p / 2)).mul (hQ.sub_const 1)
    exact (h2.const_add 1).congr_deriv (by simp; ring)
  have hs := Real.hasDerivAt_sqrt hφ.ne'
  have hsq : Real.sqrt φ ≠ 0 := (Real.sqrt_pos.2 hφ).ne'
  have hD := hN.div hs hsq
  refine hD.congr_deriv ?_
  have hQ1 := Qf_ge_one hb hφ.le
  have hQ2 := Qf_sq hb hφ.le
  have hs2 : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have hQ0 : Qf b φ ≠ 0 := by linarith
  unfold Kf
  have h : p ≠ 0 := hp.ne'
  field_simp
  rw [hs2]
  linear_combination (p * φ * (1 - φ)) * hQ2


lemma Kf_strictMonoOn {b p : ℝ} (hb : 0 < b) : StrictMonoOn (Kf b p) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx' : (1:ℝ) ≤ x := hx
  have hy' : (1:ℝ) ≤ y := hy
  have hQx := Qf_ge_one hb.le (by linarith : (0:ℝ) ≤ x)
  have hQy := Qf_ge_one hb.le (by linarith : (0:ℝ) ≤ y)
  have hQ : Qf b x < Qf b y := by
    unfold Qf; exact Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  have h1 : (Qf b x - 1) * x < (Qf b y - 1) * y := by
    nlinarith [mul_nonneg (sub_nonneg.2 hQx) (sub_nonneg.2 hxy.le),
      mul_pos (sub_pos.2 hQ) (by linarith : (0:ℝ) < y)]
  have h2 : 1 / (2 * Qf b y) ≤ 1 / (2 * Qf b x) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h3 : 0 ≤ 1 / 2 - 1 / (2 * Qf b x) := by
    have : 1 / (2 * Qf b x) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have h4 : (x - 1) * (1 / 2 - 1 / (2 * Qf b x)) ≤ (y - 1) * (1 / 2 - 1 / (2 * Qf b y)) :=
    mul_le_mul (by linarith) (by linarith) h3 (by linarith)
  unfold Kf; linarith

lemma Kf_lt_b {b b' p φ : ℝ} (hb : 0 ≤ b) (hbb : b < b') (hφ : 1 ≤ φ) :
    Kf b p φ < Kf b' p φ := by
  have hQ1 := Qf_ge_one hb (by linarith : (0:ℝ) ≤ φ)
  have hQ : Qf b φ < Qf b' φ := by
    unfold Qf; exact Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  have h1 : (Qf b φ - 1) * φ < (Qf b' φ - 1) * φ :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have h2 : 1 / (2 * Qf b' φ) ≤ 1 / (2 * Qf b φ) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h4 : (φ - 1) * (1 / 2 - 1 / (2 * Qf b φ)) ≤ (φ - 1) * (1 / 2 - 1 / (2 * Qf b' φ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold Kf; linarith

lemma Kf_lt_p {b p p' φ : ℝ} (hp : 0 < p) (hpp : p < p') : Kf b p φ < Kf b p' φ := by
  have := one_div_lt_one_div_of_lt hp hpp
  unfold Kf; rw [neg_div, neg_div]; linarith

lemma Kf_continuousOn {b p : ℝ} (hb : 0 ≤ b) : ContinuousOn (Kf b p) (Set.Ici 1) := by
  have hQ := Qf_continuous b
  unfold Kf
  apply ContinuousOn.add
  · exact continuousOn_const.add ((hQ.continuousOn.sub continuousOn_const).mul continuousOn_id)
  · apply (continuousOn_id.sub continuousOn_const).mul
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_const.mul hQ.continuousOn)
    intro x hx
    have := Qf_ge_one hb (le_trans zero_le_one hx)
    exact (by linarith : (0:ℝ) < 2 * Qf b x).ne'

lemma Kf_large {b p : ℝ} (hb : 0 < b) (hp : 0 < p) : ∃ M, 1 ≤ M ∧ 0 < Kf b p M := by
  have h1p : 0 < 1 / p := by positivity
  have h3b' : 0 < 3 / b := by positivity
  refine ⟨1 / p + 3 / b + 1, by linarith, ?_⟩
  have h3b : b * (3 / b) = 3 := by field_simp
  have hbM : 3 ≤ b * (1 / p + 3 / b + 1) := by
    have e : b * (1 / p + 3 / b + 1) = b * (1 / p) + b * (3 / b) + b := by ring
    rw [e, h3b]; nlinarith [mul_pos hb h1p]
  have hQ1 := Qf_ge_one hb.le (by linarith : (0:ℝ) ≤ 1 / p + 3 / b + 1)
  have hQ2 := Qf_sq hb.le (by linarith : (0:ℝ) ≤ 1 / p + 3 / b + 1)
  have hQ : 2 ≤ Qf b (1 / p + 3 / b + 1) := by nlinarith
  have h3 : 0 ≤ 1 / 2 - 1 / (2 * Qf b (1 / p + 3 / b + 1)) := by
    have : 1 / (2 * Qf b (1 / p + 3 / b + 1)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have h4 : 0 ≤ (1 / p + 3 / b + 1 - 1) * (1 / 2 - 1 / (2 * Qf b (1 / p + 3 / b + 1))) :=
    mul_nonneg (by linarith) h3
  have h5 : 1 / p + 3 / b + 1 ≤ (Qf b (1 / p + 3 / b + 1) - 1) * (1 / p + 3 / b + 1) := by
    nlinarith
  unfold Kf; rw [neg_div]; linarith

lemma main_char {b p : ℝ} (hb : 0 < b) (hp : 0 < p) :
    ∃ φ0, 1 ≤ φ0 ∧ 0 ≤ Kf b p φ0 ∧ (1 < φ0 → Kf b p φ0 = 0) ∧
      StrictAntiOn (Ff b p) (Set.Icc 1 φ0) ∧ StrictMonoOn (Ff b p) (Set.Ici φ0) := by
  have hcont : ∀ x, 0 < x → ContinuousAt (Ff b p) x := fun x hx =>
    (hasDerivAt_Ff hb.le hp hx).continuousAt
  have hderiv : ∀ x, 0 < x → deriv (Ff b p) x = p * Kf b p x / (2 * x * Real.sqrt x) :=
    fun x hx => (hasDerivAt_Ff hb.le hp hx).deriv
  have hden : ∀ x, 0 < x → 0 < 2 * x * Real.sqrt x := fun x hx => by
    have := Real.sqrt_pos.2 hx; positivity
  have hmono : ∀ r, 1 ≤ r → 0 ≤ Kf b p r → StrictMonoOn (Ff b p) (Set.Ici r) := by
    intro r hr hKr
    apply strictMonoOn_of_deriv_pos (convex_Ici r)
    · intro x hx
      have hx' : r ≤ x := hx
      exact (hcont x (by linarith)).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : r < x := hx
      rw [hderiv x (by linarith)]
      have hK : Kf b p r < Kf b p x :=
        Kf_strictMonoOn hb (Set.mem_Ici.2 hr) (Set.mem_Ici.2 (by linarith)) hx'
      exact div_pos (mul_pos hp (by linarith)) (hden x (by linarith))
  by_cases h1 : 0 ≤ Kf b p 1
  · refine ⟨1, le_refl _, h1, fun h => absurd h (lt_irrefl (1:ℝ)), ?_, hmono 1 le_rfl h1⟩
    rw [Set.Icc_self]; exact Set.subsingleton_singleton.strictAntiOn (Ff b p)
  · push Not at h1
    obtain ⟨M, hM1, hMpos⟩ := Kf_large hb hp
    have hivt := intermediate_value_Icc hM1
      ((Kf_continuousOn (p := p) hb.le).mono Set.Icc_subset_Ici_self)
    obtain ⟨r, ⟨hr1, hrM⟩, hr⟩ := hivt ⟨h1.le, hMpos.le⟩
    have hr1' : 1 < r := by
      rcases eq_or_lt_of_le hr1 with h | h
      · rw [← h] at hr; linarith
      · exact h
    refine ⟨r, hr1, hr.ge, fun _ => hr, ?_, hmono r hr1 hr.ge⟩
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 r)
    · intro x hx; exact (hcont x (by linarith [hx.1])).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [hderiv x (by linarith [hx.1])]
      have hK : Kf b p x < Kf b p r :=
        Kf_strictMonoOn hb (Set.mem_Ici.2 hx.1.le) (Set.mem_Ici.2 hr1) hx.2
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp (by linarith))
        (hden x (by linarith [hx.1]))

lemma min_iff {F : ℝ → ℝ} {φ0 : ℝ} (h1 : 1 ≤ φ0) (hA : StrictAntiOn F (Set.Icc 1 φ0))
    (hM : StrictMonoOn F (Set.Ici φ0)) (φ : ℝ) :
    (1 ≤ φ ∧ IsMinOn F (Set.Ici 1) φ) ↔ φ = φ0 := by
  constructor
  · rintro ⟨hφ, hmin⟩
    have hle := isMinOn_iff.1 hmin φ0 (Set.mem_Ici.2 h1)
    rcases lt_trichotomy φ φ0 with h | h | h
    · have := hA ⟨hφ, h.le⟩ ⟨h1, le_rfl⟩ h; linarith
    · exact h
    · have := hM (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h; linarith
  · intro h
    rw [h]
    refine ⟨h1, isMinOn_iff.2 fun ψ hψ => ?_⟩
    have hψ' : (1:ℝ) ≤ ψ := hψ
    rcases le_total ψ φ0 with h' | h'
    · exact hA.antitoneOn ⟨hψ', h'⟩ ⟨h1, le_rfl⟩ h'
    · exact hM.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h') h'

lemma Rtilde_eq (P : Params) (hβ : 0 < P.β) (hσ : 0 < P.sig0) {φ : ℝ} (hφ : 0 < φ) :
    Rtilde P φ = Real.sqrt (2 / Real.pi) * (P.β * P.sig0) * Ff (bP P) P.pe φ := by
  have hc : 0 < P.β * P.sig0 := mul_pos hβ hσ
  have hs : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have key : Real.sqrt (P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2)
      = P.β * P.sig0 / Real.sqrt φ * Qf (bP P) φ := by
    have h1 : P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2
        = (P.β * P.sig0 / Real.sqrt φ) ^ 2 * (1 + bP P * φ) := by
      unfold bP
      rw [div_pow, Real.sq_sqrt hφ.le]
      field_simp
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rfl
  unfold Rtilde Ff
  rw [key]
  field_simp
  ring

lemma opt_iff (P : Params) (hβ : 0 < P.β) (hσ : 0 < P.sig0) (φ : ℝ) :
    IsOptInteraction P φ ↔ (1 ≤ φ ∧ IsMinOn (Ff (bP P) P.pe) (Set.Ici 1) φ) := by
  have hk : 0 < Real.sqrt (2 / Real.pi) * (P.β * P.sig0) := by
    have : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
    have := mul_pos hβ hσ
    positivity
  unfold IsOptInteraction
  constructor
  · rintro ⟨h1, hmin⟩
    refine ⟨h1, isMinOn_iff.2 fun ψ hψ => ?_⟩
    have := isMinOn_iff.1 hmin ψ hψ
    have hψ' : (0:ℝ) < ψ := by have : (1:ℝ) ≤ ψ := hψ; linarith
    rw [Rtilde_eq P hβ hσ (by linarith), Rtilde_eq P hβ hσ hψ'] at this
    exact le_of_mul_le_mul_left this hk
  · rintro ⟨h1, hmin⟩
    refine ⟨h1, isMinOn_iff.2 fun ψ hψ => ?_⟩
    have := isMinOn_iff.1 hmin ψ hψ
    have hψ' : (0:ℝ) < ψ := by have : (1:ℝ) ≤ ψ := hψ; linarith
    rw [Rtilde_eq P hβ hσ (by linarith), Rtilde_eq P hβ hσ hψ']
    exact mul_le_mul_of_nonneg_left this hk.le

lemma statics {b p b' p' : ℝ} (hb : 0 < b) (hp : 0 < p) (hb' : 0 < b') (hp' : 0 < p')
    (hK : ∀ φ, 1 ≤ φ → Kf b p φ < Kf b' p' φ) {φ φ' : ℝ}
    (h : 1 ≤ φ ∧ IsMinOn (Ff b p) (Set.Ici 1) φ)
    (h' : 1 ≤ φ' ∧ IsMinOn (Ff b' p') (Set.Ici 1) φ') : φ' ≤ φ ∧ (1 < φ → φ' < φ) := by
  obtain ⟨φ0, h1, hK0, hKr, hA, hM⟩ := main_char hb hp
  obtain ⟨ψ0, h1', hK0', hKr', hA', hM'⟩ := main_char hb' hp'
  have e : φ = φ0 := (min_iff h1 hA hM φ).1 h
  have e' : φ' = ψ0 := (min_iff h1' hA' hM' φ').1 h'
  rw [← e] at hK0 hKr
  rw [← e'] at hK0' hKr'
  have hle : φ' ≤ φ := by
    by_contra hc
    push Not at hc
    have hφ'1 : 1 < φ' := lt_of_le_of_lt h.1 hc
    have h0 := hKr' hφ'1
    have h2 := Kf_strictMonoOn hb' (p := p') (Set.mem_Ici.2 h.1) (Set.mem_Ici.2 h'.1) hc
    have h3 := hK φ h.1
    linarith
  refine ⟨hle, fun hφ1 => lt_of_le_of_ne hle fun heq => ?_⟩
  have h0 := hKr hφ1
  have h0' := hKr' (by rw [heq]; exact hφ1)
  have h3 := hK φ h.1
  rw [heq] at h0'
  linarith

theorem old7 (P : Params) (hS : P.Standing) (hpos : 0 < P.β + P.pe) :
    (P.β = 0 → ∀ φ : ℝ, IsOptInteraction P φ ↔ φ = 1) ∧
    (0 < P.β → 0 < P.pe → ∃! φ0 : ℝ, IsOptInteraction P φ0) ∧
    (P.pe = 0 → (∀ φ : ℝ, ¬ IsOptInteraction P φ) ∧ StrictAntiOn (Rtilde P) (Set.Ici 1) ∧
        Filter.Tendsto (Rtilde P) Filter.atTop (nhds 0)) ∧
    (0 < P.β → 0 < P.pe → ∀ β' φ φ' : ℝ, P.β < β' →
        IsOptInteraction P φ → IsOptInteraction { P with β := β' } φ' →
        φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.sig0 < s' →
        IsOptInteraction P φ → IsOptInteraction { P with sig0 := s' } φ' →
        φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ p' φ φ' : ℝ, P.pe < p' → p' ≤ 1 →
        IsOptInteraction P φ → IsOptInteraction { P with pe := p' } φ' →
        φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.se < s' →
        IsOptInteraction P φ → IsOptInteraction { P with se := s' } φ' →
        φ' ≤ φ ∧ (1 < φ → φ' < φ)) := by
  obtain ⟨hσ, hse, hp0, hp1, hβ0⟩ := hS
  have hk : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hβ φ
    have hp : 0 < P.pe := by linarith
    have hR : ∀ x, Rtilde P x = Real.sqrt (2 / Real.pi) * (P.se * ((x - 1) / 2) * P.pe) := by
      intro x
      unfold Rtilde
      rw [hβ]
      simp [Real.sqrt_sq hse.le]
    unfold IsOptInteraction
    constructor
    · rintro ⟨h1, hmin⟩
      have := isMinOn_iff.1 hmin 1 (Set.mem_Ici.2 le_rfl)
      rw [hR, hR] at this
      by_contra hne
      have hlt : 1 < φ := lt_of_le_of_ne h1 (Ne.symm hne)
      have hpos' : 0 < P.se * ((φ - 1) / 2) * P.pe := by
        have : 0 < (φ - 1) / 2 := by linarith
        positivity
      have e : P.se * ((1 - 1) / 2) * P.pe = 0 := by ring
      rw [e, mul_zero] at this
      linarith [mul_pos hk hpos']
    · intro h
      rw [h]
      refine ⟨le_rfl, isMinOn_iff.2 fun ψ hψ => ?_⟩
      have hψ' : (1:ℝ) ≤ ψ := hψ
      rw [hR, hR]
      apply mul_le_mul_of_nonneg_left _ hk.le
      have : 0 ≤ (ψ - 1) / 2 := by linarith
      have e : P.se * ((1 - 1) / 2) * P.pe = 0 := by ring
      rw [e]
      positivity
  · intro hβ hp
    have hb : 0 < RoboAdvisingP51.bP P := by unfold RoboAdvisingP51.bP; positivity
    obtain ⟨φ0, h1, -, -, hA, hM⟩ := RoboAdvisingP51.main_char hb hp
    refine ⟨φ0, (RoboAdvisingP51.opt_iff P hβ hσ φ0).2 ((RoboAdvisingP51.min_iff h1 hA hM φ0).2 rfl), fun y hy => ?_⟩
    exact (RoboAdvisingP51.min_iff h1 hA hM y).1 ((RoboAdvisingP51.opt_iff P hβ hσ y).1 hy)
  · intro hp
    have hβ : 0 < P.β := by linarith
    have hc : 0 < P.β * P.sig0 := mul_pos hβ hσ
    have hR : Rtilde P = fun x => Real.sqrt (2 / Real.pi) * (P.β * P.sig0 / Real.sqrt x) := by
      funext x
      unfold Rtilde
      rw [hp]
      simp only [mul_zero, sub_zero, mul_one, add_zero]
    have hanti : StrictAntiOn (Rtilde P) (Set.Ici 1) := by
      intro x hx y hy hxy
      have hx' : (1:ℝ) ≤ x := hx
      rw [hR]
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hsxy : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt (by linarith) hxy
      exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_left hc hsx hsxy) hk
    refine ⟨fun φ hφ => ?_, hanti, ?_⟩
    · obtain ⟨h1, hmin⟩ := hφ
      have h2 := isMinOn_iff.1 hmin (φ + 1) (Set.mem_Ici.2 (by linarith))
      have h3 := hanti (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (by linarith : (1:ℝ) ≤ φ + 1))
        (by linarith : φ < φ + 1)
      linarith
    · rw [hR]
      have := (tendsto_const_nhds (x := P.β * P.sig0)).div_atTop Real.tendsto_sqrt_atTop
      simpa using this.const_mul (Real.sqrt (2 / Real.pi))
  · intro hβ hp β' φ φ' hββ hφ hφ'
    have hβ' : 0 < β' := by linarith
    have hb : 0 < RoboAdvisingP51.bP P := by unfold RoboAdvisingP51.bP; positivity
    have hb' : 0 < RoboAdvisingP51.bP { P with β := β' } := by unfold RoboAdvisingP51.bP; dsimp only; positivity
    have hlt : RoboAdvisingP51.bP { P with β := β' } < RoboAdvisingP51.bP P := by
      unfold RoboAdvisingP51.bP; dsimp only
      apply div_lt_div_of_pos_left (by positivity) (by positivity)
      have h2 : P.β ^ 2 < β' ^ 2 := by nlinarith
      have h3 : 0 < P.sig0 ^ 2 := by positivity
      nlinarith
    have h1 := (RoboAdvisingP51.opt_iff P hβ hσ φ).1 hφ
    have h2 := (RoboAdvisingP51.opt_iff { P with β := β' } hβ' hσ φ').1 hφ'
    have := RoboAdvisingP51.statics hb' hp hb hp (fun x hx => RoboAdvisingP51.Kf_lt_b hb'.le hlt hx) h2 h1
    exact ⟨this.1, fun h => this.2 (lt_of_lt_of_le h this.1)⟩
  · intro hβ hp s' φ φ' hss hφ hφ'
    have hs' : 0 < s' := by linarith
    have hb : 0 < RoboAdvisingP51.bP P := by unfold RoboAdvisingP51.bP; positivity
    have hb' : 0 < RoboAdvisingP51.bP { P with sig0 := s' } := by unfold RoboAdvisingP51.bP; dsimp only; positivity
    have hlt : RoboAdvisingP51.bP { P with sig0 := s' } < RoboAdvisingP51.bP P := by
      unfold RoboAdvisingP51.bP; dsimp only
      apply div_lt_div_of_pos_left (by positivity) (by positivity)
      have h2 : P.sig0 ^ 2 < s' ^ 2 := by nlinarith
      have h3 : 0 < P.β ^ 2 := by positivity
      nlinarith
    have h1 := (RoboAdvisingP51.opt_iff P hβ hσ φ).1 hφ
    have h2 := (RoboAdvisingP51.opt_iff { P with sig0 := s' } hβ hs' φ').1 hφ'
    have := RoboAdvisingP51.statics hb' hp hb hp (fun x hx => RoboAdvisingP51.Kf_lt_b hb'.le hlt hx) h2 h1
    exact ⟨this.1, fun h => this.2 (lt_of_lt_of_le h this.1)⟩
  · intro hβ hp p' φ φ' hpp hp1' hφ hφ'
    have hp' : 0 < p' := by linarith
    have hb : 0 < RoboAdvisingP51.bP P := by unfold RoboAdvisingP51.bP; positivity
    have h1 := (RoboAdvisingP51.opt_iff P hβ hσ φ).1 hφ
    have h2 := (RoboAdvisingP51.opt_iff { P with pe := p' } hβ hσ φ').1 hφ'
    exact RoboAdvisingP51.statics hb hp hb hp' (fun x _ => RoboAdvisingP51.Kf_lt_p hp hpp) h1 h2
  · intro hβ hp s' φ φ' hss hφ hφ'
    have hb : 0 < RoboAdvisingP51.bP P := by unfold RoboAdvisingP51.bP; positivity
    have hb' : 0 < RoboAdvisingP51.bP { P with se := s' } := by
      unfold RoboAdvisingP51.bP; dsimp only
      have : 0 < s' := by linarith
      positivity
    have hlt : RoboAdvisingP51.bP P < RoboAdvisingP51.bP { P with se := s' } := by
      unfold RoboAdvisingP51.bP; dsimp only
      apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith
    have h1 := (RoboAdvisingP51.opt_iff P hβ hσ φ).1 hφ
    have h2 := (RoboAdvisingP51.opt_iff { P with se := s' } hβ hσ φ').1 hφ'
    exact RoboAdvisingP51.statics hb hp hb' hp (fun x hx => RoboAdvisingP51.Kf_lt_b hb.le hlt hx) h1 h2

open RoboAdvising.Sensitivity

lemma opt_char (P : Params) (hβ : 0 < P.β) (hσ : 0 < P.sig0) (hse : 0 < P.se) (hp : 0 < P.pe) :
    1 ≤ optimizer P ∧ 0 ≤ Kf (bP P) P.pe (optimizer P) ∧
    (1 < optimizer P → Kf (bP P) P.pe (optimizer P) = 0) ∧
    ∀ φ, IsOptInteraction P φ ↔ φ = optimizer P := by
  have hb : 0 < bP P := by unfold bP; positivity
  obtain ⟨φ0, h1, hK0, hKr, hA, hM⟩ := main_char hb hp
  have hiff : ∀ φ, IsOptInteraction P φ ↔ φ = φ0 := fun φ =>
    (opt_iff P hβ hσ φ).trans (min_iff h1 hA hM φ)
  have hex : ∃ φ, IsOptInteraction P φ := ⟨φ0, (hiff φ0).2 rfl⟩
  have hopt : optimizer P = φ0 := by
    unfold optimizer
    rw [dif_pos hex]
    exact (hiff _).1 (Classical.choose_spec hex)
  rw [hopt]
  exact ⟨h1, hK0, hKr, hiff⟩

lemma gAux_one (P : Params) : gAux P 1 = Kf (bP P) P.pe 1 := by
  unfold gAux Kf Qf bP
  rw [show P.se ^ 2 * (1:ℝ) / (P.β ^ 2 * P.sig0 ^ 2) = P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2) * 1 by ring,
    Real.sqrt_one]
  ring

lemma opt_one_iff (P : Params) (hβ : 0 < P.β) (hσ : 0 < P.sig0) (hse : 0 < P.se) (hp : 0 < P.pe) :
    (optimizer P = 1 ↔ 0 ≤ Kf (bP P) P.pe 1) ∧ (1 < optimizer P ↔ Kf (bP P) P.pe 1 < 0) := by
  have hb : 0 < bP P := by unfold bP; positivity
  obtain ⟨h1, hK0, hKr, -⟩ := opt_char P hβ hσ hse hp
  have key : 1 < optimizer P → Kf (bP P) P.pe 1 < 0 := fun h => by
    have := Kf_strictMonoOn (p := P.pe) hb (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h1) h
    rw [hKr h] at this
    exact this
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨key, fun h => ?_⟩⟩
  · rw [h] at hK0; exact hK0
  · by_contra hne
    have := key (lt_of_le_of_ne h1 (Ne.symm hne))
    linarith
  · by_contra hne
    have e : optimizer P = 1 := le_antisymm (not_lt.1 hne) h1
    rw [e] at hK0
    linarith

noncomputable def Ka (b x : ℝ) : ℝ :=
  (Qf b x - 1) + x * b / (2 * Qf b x) + (1 / 2 - 1 / (2 * Qf b x)) + (x - 1) * b / (4 * Qf b x ^ 3)

noncomputable def Kb (b x : ℝ) : ℝ :=
  x ^ 2 / (2 * Qf b x) + x * (x - 1) / (4 * Qf b x ^ 3)

lemma Qf_gt_one {b x : ℝ} (hb : 0 < b) (hx : 0 < x) : 1 < Qf b x := by
  unfold Qf
  have h : (1:ℝ) < 1 + b * x := by nlinarith [mul_pos hb hx]
  have := Real.sqrt_lt_sqrt zero_le_one h
  simpa using this

lemma Ka_pos {b x : ℝ} (hb : 0 < b) (hx : 1 < x) : 0 < Ka b x := by
  have hQ := Qf_gt_one hb (by linarith : (0:ℝ) < x)
  have hQ0 : 0 < Qf b x := by linarith
  have h1 : 0 < x * b / (2 * Qf b x) := by
    have : 0 < x := by linarith
    positivity
  have h2 : 1 / (2 * Qf b x) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h3 : 0 ≤ (x - 1) * b / (4 * Qf b x ^ 3) :=
    div_nonneg (mul_nonneg (by linarith) hb.le) (by positivity)
  unfold Ka
  linarith

lemma Kb_pos {b x : ℝ} (hb : 0 < b) (hx : 1 < x) : 0 < Kb b x := by
  have hQ := Qf_gt_one hb (by linarith : (0:ℝ) < x)
  have hQ0 : 0 < Qf b x := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x ^ 2 / (2 * Qf b x) := by positivity
  have h3 : 0 ≤ x * (x - 1) / (4 * Qf b x ^ 3) :=
    div_nonneg (mul_nonneg hx0.le (by linarith)) (by positivity)
  unfold Kb
  linarith

lemma hasDerivAt_Kf_x {b p x : ℝ} (hb : 0 ≤ b) (hx : 0 < x) : HasDerivAt (Kf b p) (Ka b x) x := by
  have hQ := hasDerivAt_Qf hb hx
  have hQ0 : 0 < Qf b x := by linarith [Qf_ge_one hb hx.le]
  have h1 := (hQ.sub_const 1).mul (hasDerivAt_id x)
  have h2 := (hasDerivAt_const x (1:ℝ)).div (hQ.const_mul 2) (mul_pos two_pos hQ0).ne'
  have h3 := ((hasDerivAt_const x (-1 / p)).add h1).add
    (((hasDerivAt_id x).sub_const 1).mul ((hasDerivAt_const x (1 / 2 : ℝ)).sub h2))
  unfold Kf
  refine h3.congr_deriv ?_
  unfold Ka
  simp only [id, Pi.sub_apply, Pi.div_apply]
  field_simp
  ring

lemma hasDerivAt_Kf_t {B Pp : ℝ → ℝ} {B' P' t0 x : ℝ} (hB : HasDerivAt B B' t0)
    (hP : HasDerivAt Pp P' t0) (hb : 0 ≤ B t0) (hp : Pp t0 ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun t => Kf (B t) (Pp t) x) (Kb (B t0) x * B' + P' / Pp t0 ^ 2) t0 := by
  have hpos : 0 < 1 + B t0 * x := by positivity
  have hQ : HasDerivAt (fun t => Qf (B t) x) (B' * x / (2 * Qf (B t0) x)) t0 := by
    have := ((hB.mul_const x).const_add 1).sqrt hpos.ne'
    unfold Qf
    exact this
  have hQ0 : 0 < Qf (B t0) x := by linarith [Qf_ge_one hb hx.le]
  have h0 := (hasDerivAt_const t0 (-1 : ℝ)).div hP hp
  have h1 := (hQ.sub_const 1).mul_const x
  have h2 := (hasDerivAt_const t0 (1:ℝ)).div (hQ.const_mul 2) (mul_pos two_pos hQ0).ne'
  have h3 := (h0.add h1).add
    ((hasDerivAt_const t0 (x - 1)).mul ((hasDerivAt_const t0 (1 / 2 : ℝ)).sub h2))
  unfold Kf
  refine h3.congr_deriv ?_
  unfold Kb
  field_simp
  ring

lemma diffAt_Kf {B Pp : ℝ → ℝ} {t0 x0 : ℝ} (hB : DifferentiableAt ℝ B t0)
    (hP : DifferentiableAt ℝ Pp t0) (hb : 0 ≤ B t0) (hp : Pp t0 ≠ 0) (hx : 0 < x0) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => Kf (B q.2) (Pp q.2) q.1) (x0, t0) := by
  have hB2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.2) (x0, t0) :=
    hB.comp (x0, t0) differentiableAt_snd
  have hP2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => Pp q.2) (x0, t0) :=
    hP.comp (x0, t0) differentiableAt_snd
  have hpos : 0 < 1 + B t0 * x0 := by positivity
  have hS : DifferentiableAt ℝ (fun q : ℝ × ℝ => Qf (B q.2) q.1) (x0, t0) := by
    unfold Qf
    exact ((differentiableAt_const _).add (hB2.mul differentiableAt_fst)).sqrt hpos.ne'
  have hQ0 : 0 < Qf (B t0) x0 := by linarith [Qf_ge_one hb hx.le]
  have hp' : (fun q : ℝ × ℝ => Pp q.2) (x0, t0) ≠ 0 := hp
  have hQ0' : (fun q : ℝ × ℝ => 2 * Qf (B q.2) q.1) (x0, t0) ≠ 0 := (mul_pos two_pos hQ0).ne'
  have hd : DifferentiableAt ℝ (fun t => -1 / Pp t) t0 := (differentiableAt_const _).div hP hp
  have hD1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => -1 / Pp q.2) (x0, t0) :=
    DifferentiableAt.comp (g := fun t => -1 / Pp t) (f := Prod.snd) (x0, t0) hd differentiableAt_snd
  have hD2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => 2 * Qf (B q.2) q.1) (x0, t0) :=
    (differentiableAt_const _).mul hS
  have hD3 : DifferentiableAt ℝ (fun q : ℝ × ℝ => 1 / (2 * Qf (B q.2) q.1)) (x0, t0) :=
    by simpa only [one_div] using hD2.fun_inv hQ0'
  have hD4 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (Qf (B q.2) q.1 - 1) * q.1) (x0, t0) :=
    (hS.sub (differentiableAt_const _)).mul differentiableAt_fst
  have hD5 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (q.1 - 1) * (1 / 2 - 1 / (2 * Qf (B q.2) q.1)))
      (x0, t0) :=
    (differentiableAt_fst.sub (differentiableAt_const _)).mul ((differentiableAt_const _).sub hD3)
  unfold Kf
  exact (hD1.add hD4).add hD5

lemma clm_prod_apply (L : ℝ × ℝ →L[ℝ] ℝ) (u s : ℝ) :
    L (u, s) = u * L (1, 0) + s * L (0, 1) := by
  have : ((u, s) : ℝ × ℝ) = u • ((1:ℝ), (0:ℝ)) + s • ((0:ℝ), (1:ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma implicit_deriv {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {x0 t0 a c : ℝ}
    (hF : DifferentiableAt ℝ F (x0, t0))
    (ha : HasDerivAt (fun x => F (x, t0)) a x0) (hc : HasDerivAt (fun t => F (x0, t)) c t0)
    (ha0 : a ≠ 0) (hg : ContinuousAt g t0) (hg0 : g t0 = x0)
    (hz : ∀ᶠ t in nhds t0, F (g t, t) = F (x0, t0)) :
    HasDerivAt g (-c / a) t0 := by
  have hFL : HasFDerivAt F (fderiv ℝ F (x0, t0)) (x0, t0) := hF.hasFDerivAt
  set L := fderiv ℝ F (x0, t0) with hL
  have hLa : L (1, 0) = a := by
    have h1 : HasDerivAt (fun x : ℝ => ((x, t0) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) x0 :=
      (hasDerivAt_id x0).prodMk (hasDerivAt_const x0 t0)
    exact (hFL.comp_hasDerivAt x0 h1).unique ha
  have hLc : L (0, 1) = c := by
    have h1 : HasDerivAt (fun t : ℝ => ((x0, t) : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) t0 :=
      (hasDerivAt_const t0 x0).prodMk (hasDerivAt_id t0)
    exact (hFL.comp_hasDerivAt t0 h1).unique hc
  have hφ : Filter.Tendsto (fun t => ((g t, t) : ℝ × ℝ)) (nhds t0) (nhds (x0, t0)) := by
    have := hg.prodMk continuousAt_id
    rw [ContinuousAt, hg0] at this
    exact this
  have h2 := hFL.isLittleO.comp_tendsto hφ
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hA : 0 < |a| := abs_pos.2 ha0
  have hC : 0 ≤ |c| := abs_nonneg c
  set δ := min (|a| / 2) (ε * |a| ^ 2 / (2 * |a| + 2 * |c|)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ |a| / 2 := min_le_left _ _
  have hδ2 : δ * (2 * |a| + 2 * |c|) ≤ ε * |a| ^ 2 := by
    have := min_le_right (|a| / 2) (ε * |a| ^ 2 / (2 * |a| + 2 * |c|))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  filter_upwards [Asymptotics.isLittleO_iff.1 h2 hδ0, hz] with t ht hzt
  simp only [Function.comp] at ht
  rw [hzt, sub_self, zero_sub, norm_neg, Prod.mk_sub_mk, clm_prod_apply, hLa, hLc,
    Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at ht
  rw [hg0, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  set u := g t - x0
  set s := t - t0
  have hU := abs_nonneg u
  have hS := abs_nonneg s
  have h1 : |u * a + s * c| ≤ δ * (|u| + |s|) := by
    refine ht.trans (mul_le_mul_of_nonneg_left ?_ hδ0.le)
    exact max_le (by linarith) (by linarith)
  have h2' : |a| * |u| ≤ |u * a + s * c| + |c| * |s| := by
    have e : a * u = (u * a + s * c) - s * c := by ring
    rw [← abs_mul, e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, mul_comm |s|]
  have h3 : δ * |u| ≤ |a| / 2 * |u| := mul_le_mul_of_nonneg_right hδ1 hU
  have h3' : δ * |s| ≤ |a| / 2 * |s| := mul_le_mul_of_nonneg_right hδ1 hS
  have h4 : |a| * |u| ≤ (|a| + 2 * |c|) * |s| := by nlinarith
  have h5a : |a| * |u * a + s * c| ≤ |a| * (δ * (|u| + |s|)) := mul_le_mul_of_nonneg_left h1 hA.le
  have h5b : δ * (|a| * |u|) ≤ δ * ((|a| + 2 * |c|) * |s|) := mul_le_mul_of_nonneg_left h4 hδ0.le
  have h5c : δ * (2 * |a| + 2 * |c|) * |s| ≤ ε * |a| ^ 2 * |s| := mul_le_mul_of_nonneg_right hδ2 hS
  have h5 : |a| * |u * a + s * c| ≤ |a| * (ε * |a| * |s|) := by nlinarith
  have h6 : |u * a + s * c| ≤ ε * |a| * |s| := le_of_mul_le_mul_left h5 hA
  have e : u - s * (-c / a) = (u * a + s * c) / a := by field_simp; ring
  rw [e, abs_div]
  rw [div_le_iff₀ hA]
  linarith

lemma root_cont {K : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {t0 : ℝ}
    (hmono : ∀ᶠ t in nhds t0, StrictMonoOn (K t) (Set.Ici 1))
    (hroot : ∀ᶠ t in nhds t0, 1 ≤ g t ∧ K t (g t) = 0)
    (hcont : ∀ x, 1 ≤ x → ContinuousAt (fun t => K t x) t0)
    (h1 : 1 < g t0) : ContinuousAt g t0 := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hm0 := hmono.self_of_nhds
  have hr0 := hroot.self_of_nhds
  set e := min (ε / 2) ((g t0 - 1) / 2) with he_def
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have he1 : e ≤ ε / 2 := min_le_left _ _
  have he2 : e ≤ (g t0 - 1) / 2 := min_le_right _ _
  have hlo : K t0 (g t0 - e) < 0 := by
    have := hm0 (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hr0.1) (by linarith : g t0 - e < g t0)
    rw [hr0.2] at this
    exact this
  have hhi : 0 < K t0 (g t0 + e) := by
    have := hm0 (Set.mem_Ici.2 hr0.1) (Set.mem_Ici.2 (by linarith)) (by linarith : g t0 < g t0 + e)
    rw [hr0.2] at this
    exact this
  have ev1 := (hcont (g t0 - e) (by linarith)).eventually (gt_mem_nhds hlo)
  have ev2 := (hcont (g t0 + e) (by linarith)).eventually (lt_mem_nhds hhi)
  filter_upwards [hmono, hroot, ev1, ev2] with t hm hr hl hh
  rw [Real.dist_eq, abs_lt]
  have hA : g t0 - e < g t := by
    by_contra hc
    push Not at hc
    have := (hm.le_iff_le (Set.mem_Ici.2 hr.1) (Set.mem_Ici.2 (by linarith))).2 hc
    linarith [hr.2]
  have hB : g t < g t0 + e := by
    by_contra hc
    push Not at hc
    have := (hm.le_iff_le (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hr.1)).2 hc
    linarith [hr.2]
  constructor <;> linarith

lemma opt_deriv_generic (Pf : ℝ → Params) (B Pp : ℝ → ℝ) {t0 B' P' : ℝ}
    (hBd : ∀ t, bP (Pf t) = B t) (hPd : ∀ t, (Pf t).pe = Pp t)
    (hev : ∀ᶠ t in nhds t0, 0 < (Pf t).β ∧ 0 < (Pf t).sig0 ∧ 0 < (Pf t).se ∧ 0 < (Pf t).pe)
    (hB : HasDerivAt B B' t0) (hP : HasDerivAt Pp P' t0)
    (hneg : Kf (B t0) (Pp t0) 1 < 0) :
    ∃ a cb : ℝ, 0 < a ∧ 0 < cb ∧
      HasDerivAt (fun t => optimizer (Pf t)) (-(cb * B' + P' / Pp t0 ^ 2) / a) t0 := by
  obtain ⟨hβ0, hσ0, hse0, hp0⟩ := hev.self_of_nhds
  have hb0 : 0 < B t0 := by rw [← hBd]; unfold bP; positivity
  have hpp : 0 < Pp t0 := by rw [← hPd]; exact hp0
  have hKt : ∀ x, 0 < x → HasDerivAt (fun t => Kf (B t) (Pp t) x)
      (Kb (B t0) x * B' + P' / Pp t0 ^ 2) t0 := fun x hx =>
    hasDerivAt_Kf_t hB hP hb0.le hpp.ne' hx
  have hneg_ev : ∀ᶠ t in nhds t0, Kf (B t) (Pp t) 1 < 0 :=
    (hKt 1 one_pos).continuousAt.eventually (gt_mem_nhds hneg)
  have hroot : ∀ᶠ t in nhds t0, 1 < optimizer (Pf t) ∧ Kf (B t) (Pp t) (optimizer (Pf t)) = 0 := by
    filter_upwards [hev, hneg_ev] with t ht hn
    obtain ⟨h1, h2, h3, h4⟩ := ht
    have hc := opt_char (Pf t) h1 h2 h3 h4
    have hoi := opt_one_iff (Pf t) h1 h2 h3 h4
    rw [hBd, hPd] at hc hoi
    have hgt : 1 < optimizer (Pf t) := hoi.2.2 hn
    exact ⟨hgt, hc.2.2.1 hgt⟩
  obtain ⟨hg1, hgK⟩ := hroot.self_of_nhds
  have hmono : ∀ᶠ t in nhds t0, StrictMonoOn (Kf (B t) (Pp t)) (Set.Ici 1) := by
    have hBev : ∀ᶠ t in nhds t0, 0 < B t := hB.continuousAt.eventually (lt_mem_nhds hb0)
    filter_upwards [hBev] with t ht using Kf_strictMonoOn ht
  have hcont : ContinuousAt (fun t => optimizer (Pf t)) t0 :=
    root_cont (K := fun t x => Kf (B t) (Pp t) x) hmono (hroot.mono fun t h => ⟨h.1.le, h.2⟩)
      (fun x hx => (hKt x (by linarith)).continuousAt) hg1
  refine ⟨Ka (B t0) (optimizer (Pf t0)), Kb (B t0) (optimizer (Pf t0)), Ka_pos hb0 hg1,
    Kb_pos hb0 hg1, ?_⟩
  have hx0 : 0 < optimizer (Pf t0) := by linarith
  refine implicit_deriv (F := fun q : ℝ × ℝ => Kf (B q.2) (Pp q.2) q.1)
    (x0 := optimizer (Pf t0))
    (diffAt_Kf hB.differentiableAt hP.differentiableAt hb0.le hpp.ne' hx0)
    (hasDerivAt_Kf_x (p := Pp t0) hb0.le hx0) (hKt _ hx0) (Ka_pos hb0 hg1).ne' hcont rfl ?_
  filter_upwards [hroot] with t ht
  show Kf (B t) (Pp t) (optimizer (Pf t)) = Kf (B t0) (Pp t0) (optimizer (Pf t0))
  rw [ht.2, hgK]

lemma opt_corner_generic (Pf : ℝ → Params) (B Pp : ℝ → ℝ) {t0 B' P' : ℝ}
    (hBd : ∀ t, bP (Pf t) = B t) (hPd : ∀ t, (Pf t).pe = Pp t)
    (hev : ∀ᶠ t in nhds t0, 0 < (Pf t).β ∧ 0 < (Pf t).sig0 ∧ 0 < (Pf t).se ∧ 0 < (Pf t).pe)
    (hB : HasDerivAt B B' t0) (hP : HasDerivAt Pp P' t0)
    (hposK : 0 < Kf (B t0) (Pp t0) 1) :
    (∀ᶠ t in nhds t0, optimizer (Pf t) = 1) ∧ HasDerivAt (fun t => optimizer (Pf t)) 0 t0 := by
  obtain ⟨hβ0, hσ0, hse0, hp0⟩ := hev.self_of_nhds
  have hb0 : 0 < B t0 := by rw [← hBd]; unfold bP; positivity
  have hpp : 0 < Pp t0 := by rw [← hPd]; exact hp0
  have hK1 := (hasDerivAt_Kf_t (x := 1) hB hP hb0.le hpp.ne' one_pos).continuousAt.eventually
    (lt_mem_nhds hposK)
  have hev1 : ∀ᶠ t in nhds t0, optimizer (Pf t) = 1 := by
    filter_upwards [hev, hK1] with t ht hk
    obtain ⟨h1, h2, h3, h4⟩ := ht
    have hoi := opt_one_iff (Pf t) h1 h2 h3 h4
    rw [hBd, hPd] at hoi
    exact hoi.1.2 hk.le
  exact ⟨hev1, (hasDerivAt_const t0 (1:ℝ)).congr_of_eventuallyEq hev1⟩

end RoboAdvisingP51

open RoboAdvising.Interaction RoboAdvising.Sensitivity in
theorem solution (P : Params) (hS : P.Standing)
    (hpos : 0 < P.β + P.pe) :
    (P.β = 0 → ∀ φ : ℝ, IsOptInteraction P φ ↔ φ = 1) ∧
    (0 < P.β → 0 < P.pe → ∃! φ0 : ℝ, IsOptInteraction P φ0) ∧
    (P.pe = 0 → (∀ φ : ℝ, ¬ IsOptInteraction P φ) ∧
      StrictAntiOn (Rtilde P) (Set.Ici 1) ∧
      Filter.Tendsto (Rtilde P) Filter.atTop (nhds 0)) ∧
    (0 < P.β → 0 < P.pe → ∀ β' φ φ' : ℝ, P.β < β' →
      IsOptInteraction P φ → IsOptInteraction { P with β := β' } φ' →
      φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.sig0 < s' →
      IsOptInteraction P φ → IsOptInteraction { P with sig0 := s' } φ' →
      φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ p' φ φ' : ℝ, P.pe < p' → p' ≤ 1 →
      IsOptInteraction P φ → IsOptInteraction { P with pe := p' } φ' →
      φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.se < s' →
      IsOptInteraction P φ → IsOptInteraction { P with se := s' } φ' →
      φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (P.β = 0 → optimizer P = 1) ∧
    (0 < P.β → 0 < P.pe →
      (∀ φ : ℝ, IsOptInteraction P φ ↔ φ = optimizer P) ∧
      (optimizer P = 1 ↔ 0 ≤ gAux P 1) ∧
      (1 < optimizer P ↔ gAux P 1 < 0) ∧
      (gAux P 1 < 0 → ∃ dβ dσ dp ds : ℝ,
        HasDerivAt (fun b : ℝ => optimizer { P with β := b }) dβ P.β ∧
        HasDerivAt (fun v : ℝ => optimizer { P with sig0 := v }) dσ P.sig0 ∧
        HasDerivWithinAt (fun q : ℝ => optimizer { P with pe := q }) dp
          (Set.Ioc 0 1) P.pe ∧
        (P.pe < 1 → HasDerivAt (fun q : ℝ => optimizer { P with pe := q }) dp P.pe) ∧
        HasDerivAt (fun v : ℝ => optimizer { P with se := v }) ds P.se ∧
        0 < dβ ∧ 0 < dσ ∧ dp < 0 ∧ ds < 0) ∧
      (0 < gAux P 1 →
        (∀ᶠ b : ℝ in nhds P.β, optimizer { P with β := b } = 1) ∧
        (∀ᶠ v : ℝ in nhds P.sig0, optimizer { P with sig0 := v } = 1) ∧
        (∀ᶠ q : ℝ in nhdsWithin P.pe (Set.Ioc 0 1), optimizer { P with pe := q } = 1) ∧
        (∀ᶠ v : ℝ in nhds P.se, optimizer { P with se := v } = 1) ∧
        HasDerivAt (fun b : ℝ => optimizer { P with β := b }) 0 P.β ∧
        HasDerivAt (fun v : ℝ => optimizer { P with sig0 := v }) 0 P.sig0 ∧
        HasDerivWithinAt (fun q : ℝ => optimizer { P with pe := q }) 0
          (Set.Ioc 0 1) P.pe ∧
        (P.pe < 1 → HasDerivAt (fun q : ℝ => optimizer { P with pe := q }) 0 P.pe) ∧
        HasDerivAt (fun v : ℝ => optimizer { P with se := v }) 0 P.se)) := by
  have h7 := RoboAdvisingP51.old7 P hS hpos
  obtain ⟨hσ, hse, hp0, hp1, hβ0⟩ := hS
  refine ⟨h7.1, h7.2.1, h7.2.2.1, h7.2.2.2.1, h7.2.2.2.2.1, h7.2.2.2.2.2.1, h7.2.2.2.2.2.2, ?_, ?_⟩
  · intro hβ
    have h := h7.1 hβ
    have hex : ∃ φ, IsOptInteraction P φ := ⟨1, (h 1).2 rfl⟩
    unfold optimizer
    rw [dif_pos hex]
    exact (h _).1 (Classical.choose_spec hex)
  · intro hβ hp
    obtain ⟨-, -, -, hiff⟩ := RoboAdvisingP51.opt_char P hβ hσ hse hp
    have hoi := RoboAdvisingP51.opt_one_iff P hβ hσ hse hp
    rw [← RoboAdvisingP51.gAux_one P] at hoi
    have evβ : ∀ᶠ b in nhds P.β, 0 < ({ P with β := b } : Params).β ∧
        0 < ({ P with β := b } : Params).sig0 ∧ 0 < ({ P with β := b } : Params).se ∧
        0 < ({ P with β := b } : Params).pe := by
      filter_upwards [lt_mem_nhds hβ] with b hb
      exact ⟨hb, hσ, hse, hp⟩
    have evσ : ∀ᶠ v in nhds P.sig0, 0 < ({ P with sig0 := v } : Params).β ∧
        0 < ({ P with sig0 := v } : Params).sig0 ∧ 0 < ({ P with sig0 := v } : Params).se ∧
        0 < ({ P with sig0 := v } : Params).pe := by
      filter_upwards [lt_mem_nhds hσ] with v hv
      exact ⟨hβ, hv, hse, hp⟩
    have evp : ∀ᶠ q in nhds P.pe, 0 < ({ P with pe := q } : Params).β ∧
        0 < ({ P with pe := q } : Params).sig0 ∧ 0 < ({ P with pe := q } : Params).se ∧
        0 < ({ P with pe := q } : Params).pe := by
      filter_upwards [lt_mem_nhds hp] with q hq
      exact ⟨hβ, hσ, hse, hq⟩
    have evs : ∀ᶠ v in nhds P.se, 0 < ({ P with se := v } : Params).β ∧
        0 < ({ P with se := v } : Params).sig0 ∧ 0 < ({ P with se := v } : Params).se ∧
        0 < ({ P with se := v } : Params).pe := by
      filter_upwards [lt_mem_nhds hse] with v hv
      exact ⟨hβ, hσ, hv, hp⟩
    have dBβ : HasDerivAt (fun b : ℝ => P.se ^ 2 / (b ^ 2 * P.sig0 ^ 2))
        (-(2 * P.se ^ 2 / (P.β ^ 3 * P.sig0 ^ 2))) P.β := by
      have h := (hasDerivAt_const P.β (P.se ^ 2)).div
        ((hasDerivAt_pow 2 P.β).mul_const (P.sig0 ^ 2)) (by positivity)
      refine h.congr_deriv ?_
      field_simp
      ring
    have dBσ : HasDerivAt (fun v : ℝ => P.se ^ 2 / (P.β ^ 2 * v ^ 2))
        (-(2 * P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 3))) P.sig0 := by
      have h := (hasDerivAt_const P.sig0 (P.se ^ 2)).div
        ((hasDerivAt_pow 2 P.sig0).const_mul (P.β ^ 2)) (by positivity)
      refine h.congr_deriv ?_
      field_simp
      ring
    have dBs : HasDerivAt (fun v : ℝ => v ^ 2 / (P.β ^ 2 * P.sig0 ^ 2))
        (2 * P.se / (P.β ^ 2 * P.sig0 ^ 2)) P.se := by
      have h := (hasDerivAt_pow 2 P.se).div_const (P.β ^ 2 * P.sig0 ^ 2)
      refine h.congr_deriv ?_
      field_simp
      ring
    refine ⟨fun φ => hiff φ, hoi.1, hoi.2, ?_, ?_⟩
    · intro hg
      have hK : RoboAdvisingP51.Kf (RoboAdvisingP51.bP P) P.pe 1 < 0 := by
        rw [← RoboAdvisingP51.gAux_one]; exact hg
      obtain ⟨a1, c1, ha1, hc1, D1⟩ := RoboAdvisingP51.opt_deriv_generic
        (fun b => { P with β := b }) (fun b => P.se ^ 2 / (b ^ 2 * P.sig0 ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evβ dBβ (hasDerivAt_const _ _) hK
      obtain ⟨a2, c2, ha2, hc2, D2⟩ := RoboAdvisingP51.opt_deriv_generic
        (fun v => { P with sig0 := v }) (fun v => P.se ^ 2 / (P.β ^ 2 * v ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evσ dBσ (hasDerivAt_const _ _) hK
      obtain ⟨a3, c3, ha3, hc3, D3⟩ := RoboAdvisingP51.opt_deriv_generic
        (fun q => { P with pe := q }) (fun _ => RoboAdvisingP51.bP P) (fun q => q)
        (fun _ => rfl) (fun _ => rfl) evp (hasDerivAt_const _ _) (hasDerivAt_id' P.pe) hK
      obtain ⟨a4, c4, ha4, hc4, D4⟩ := RoboAdvisingP51.opt_deriv_generic
        (fun v => { P with se := v }) (fun v => v ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evs dBs (hasDerivAt_const _ _) hK
      refine ⟨_, _, _, _, D1, D2, D3.hasDerivWithinAt, fun _ => D3, D4, ?_, ?_, ?_, ?_⟩
      · have : c1 * (-(2 * P.se ^ 2 / (P.β ^ 3 * P.sig0 ^ 2))) < 0 :=
          mul_neg_of_pos_of_neg hc1 (neg_neg_of_pos (by positivity))
        rw [zero_div, add_zero]
        exact div_pos (by linarith) ha1
      · have : c2 * (-(2 * P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 3))) < 0 :=
          mul_neg_of_pos_of_neg hc2 (neg_neg_of_pos (by positivity))
        rw [zero_div, add_zero]
        exact div_pos (by linarith) ha2
      · rw [mul_zero, zero_add]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) ha3
      · rw [zero_div, add_zero]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hc4 (by positivity))) ha4
    · intro hg
      have hK : 0 < RoboAdvisingP51.Kf (RoboAdvisingP51.bP P) P.pe 1 := by
        rw [← RoboAdvisingP51.gAux_one]; exact hg
      obtain ⟨E1, Z1⟩ := RoboAdvisingP51.opt_corner_generic
        (fun b => { P with β := b }) (fun b => P.se ^ 2 / (b ^ 2 * P.sig0 ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evβ dBβ (hasDerivAt_const _ _) hK
      obtain ⟨E2, Z2⟩ := RoboAdvisingP51.opt_corner_generic
        (fun v => { P with sig0 := v }) (fun v => P.se ^ 2 / (P.β ^ 2 * v ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evσ dBσ (hasDerivAt_const _ _) hK
      obtain ⟨E3, Z3⟩ := RoboAdvisingP51.opt_corner_generic
        (fun q => { P with pe := q }) (fun _ => RoboAdvisingP51.bP P) (fun q => q)
        (fun _ => rfl) (fun _ => rfl) evp (hasDerivAt_const _ _) (hasDerivAt_id' P.pe) hK
      obtain ⟨E4, Z4⟩ := RoboAdvisingP51.opt_corner_generic
        (fun v => { P with se := v }) (fun v => v ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) (fun _ => P.pe)
        (fun _ => rfl) (fun _ => rfl) evs dBs (hasDerivAt_const _ _) hK
      exact ⟨E1, E2, E3.filter_mono nhdsWithin_le_nhds, E4, Z1, Z2, Z3.hasDerivWithinAt,
        fun _ => Z3, Z4⟩
