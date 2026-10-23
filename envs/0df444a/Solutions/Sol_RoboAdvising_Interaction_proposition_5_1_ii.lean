-- Prove2me | solution 1 for RoboAdvising.Interaction.proposition_5_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T03:35:55.000584+00:00
-- url     : https://prove2.me/submissions/f64bb51b-ddef-4e28-95c5-958f75175070

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

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

end RoboAdvisingP51

open RoboAdvising.Interaction in
theorem solution (P : Params) (hS : P.Standing) (hpos : 0 < P.β + P.pe) :
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
