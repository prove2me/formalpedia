-- Prove2me | solution 1 for RareDisease.ExogOutcome.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:14:44.365811+00:00
-- url     : https://prove2.me/submissions/39625ac5-2067-4be0-9edc-ef5d27b5e42d

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting
import Theorems.Thm_RareDisease_ExogOutcome_best_response
import Theorems.Thm_RareDisease_ExogOutcome_reduced_problem
import Theorems.Thm_RareDisease_ExogOutcome_reduced_monotone

set_option maxHeartbeats 4000000

open RareDisease.ExogOutcome

namespace DS19B

noncomputable section

/-! ## The reduced problem `W`, `M` as functions of the policy `(α,β)` -/

/-- `q = 1 - (1-β)p`. -/
noncomputable def qf (p β : ℝ) : ℝ := 1 - (1 - β) * p

/-- The patient welfare at the manufacturer's best response. -/
noncomputable def Wf (k p : ℝ) (α β : ℝ) : ℝ :=
  p * qf p β ^ 3 / (4 * (1 - α) * k)

/-- The government spending at the manufacturer's best response. -/
noncomputable def Mf (k p : ℝ) (α β : ℝ) : ℝ :=
  α * p ^ 2 * qf p β ^ 2 / (4 * (1 - α) ^ 2 * k)
    + β * p ^ 2 * qf p β ^ 2 / (2 * (1 - α) * k)

lemma qf_pos (p β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < qf p β := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  unfold qf
  have h1 : (1 - β) * p ≤ 1 * p :=
    mul_le_mul_of_nonneg_right (show 1 - β ≤ 1 by linarith) hp0.le
  linarith

lemma qf_ne (p β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    qf p β ≠ 0 := (qf_pos p β hβ hp0 hp1).ne'

/-- The best-response set is the singleton given by (19). -/
lemma br_eq (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) :
    BR k p α β = {p * qf p β / (2 * (1 - α) * k)} := by
  simpa [qf] using best_response k p α β hk hp0 hp1 hpol

/-- Characterization of `IsOptimal` through `Wf` and `Mf`. -/
theorem isOptimal_iff (k p B α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    IsOptimal k p B α β ↔
      RareDisease.Endogenous.IsPolicy α β ∧ Mf k p α β ≤ B ∧
        ∀ α' β', RareDisease.Endogenous.IsPolicy α' β' → Mf k p α' β' ≤ B →
          Wf k p α' β' ≤ Wf k p α β := by
  constructor
  · rintro ⟨hpol, e, he, hspend, hbest⟩
    have heBR : e ∈ BR k p α β := he
    rw [br_eq k p α β hk hp0 hp1 hpol] at he
    simp only [Set.mem_singleton_iff] at he
    have hred := reduced_problem k p α β hk hp0 hp1 hpol e heBR
    refine ⟨hpol, ?_, ?_⟩
    · have h := hspend
      rw [hred.2] at h
      simpa [Mf, qf] using h
    · intro α' β' hpol' hM
      have hbr' : p * qf p β' / (2 * (1 - α') * k) ∈ BR k p α' β' := by
        rw [br_eq k p α' β' hk hp0 hp1 hpol']
        simp
      have hred' := reduced_problem k p α' β' hk hp0 hp1 hpol'
        (p * qf p β' / (2 * (1 - α') * k)) hbr'
      have hspend' : spend k p α' β' (p * qf p β' / (2 * (1 - α') * k)) ≤ B := by
        rw [hred'.2]; exact hM
      have hle := hbest α' β' hpol' _ hbr' hspend'
      rw [hred'.1, hred.1] at hle
      simpa [Wf, qf] using hle
  · rintro ⟨hpol, hM, hW⟩
    have hbr : p * qf p β / (2 * (1 - α) * k) ∈ BR k p α β := by
      rw [br_eq k p α β hk hp0 hp1 hpol]
      simp
    have hred := reduced_problem k p α β hk hp0 hp1 hpol
      (p * qf p β / (2 * (1 - α) * k)) hbr
    refine ⟨hpol, p * qf p β / (2 * (1 - α) * k), hbr, ?_, ?_⟩
    · rw [hred.2]; exact hM
    · intro α' β' hpol' e' he' hspend'
      have hred' := reduced_problem k p α' β' hk hp0 hp1 hpol' e' he'
      have hM' : Mf k p α' β' ≤ B := by
        have h := hspend'
        rw [hred'.2] at h
        simpa [Mf, qf] using h
      have := hW α' β' hpol' hM'
      rw [hred'.1, hred.1]
      simpa [Wf, qf] using this

/-! ## The explicit binding policy `α*(β)` -/

/-- `σ = 1 - 2β`. -/
noncomputable def sg (β : ℝ) : ℝ := 1 - 2 * β

/-- `w(β) = √(σ² + 4c/q²)`. -/
noncomputable def wv (c p β : ℝ) : ℝ := Real.sqrt (sg β ^ 2 + 4 * c / qf p β ^ 2)

/-- `A(β) = w + σ`. -/
noncomputable def Av (c p β : ℝ) : ℝ := wv c p β + sg β

/-- The binding value of `α` for a given `β`, solving `M(α,β) = B`. -/
noncomputable def al (c p β : ℝ) : ℝ := 1 - 2 / Av c p β

lemma sg_eq (β : ℝ) : sg β = 1 - 2 * β := rfl

lemma wv_sq (c p β : ℝ) (hc : 0 ≤ c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    wv c p β ^ 2 = sg β ^ 2 + 4 * c / qf p β ^ 2 := by
  unfold wv
  rw [Real.sq_sqrt]
  have hq := qf_ne p β hβ hp0 hp1
  have : 0 ≤ 4 * c / qf p β ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  linarith [sq_nonneg (sg β)]

lemma Av_pos (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < Av c p β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have hw0 : 0 ≤ wv c p β := Real.sqrt_nonneg _
  have hc4 : 0 < 4 * c / qf p β ^ 2 := div_pos (by linarith) (sq_pos_of_ne_zero hq)
  have hlt : sg β ^ 2 < wv c p β ^ 2 := by rw [hw2]; linarith
  have h1 : -(wv c p β) < sg β := by
    by_contra h
    push_neg at h
    have hwle : wv c p β ≤ -sg β := by linarith
    have : wv c p β ^ 2 ≤ (-sg β) ^ 2 := pow_le_pow_left₀ hw0 hwle 2
    nlinarith [this]
  have h2 : sg β < wv c p β := by
    by_contra h
    push_neg at h
    have : wv c p β ^ 2 ≤ sg β ^ 2 := pow_le_pow_left₀ hw0 h 2
    linarith
  unfold Av
  linarith

lemma Av_ne (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    Av c p β ≠ 0 := (Av_pos c p β hc hβ hp0 hp1).ne'

lemma al_lt_one (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    al c p β < 1 := by
  unfold al
  have hA := Av_pos c p β hc hβ hp0 hp1
  have : 0 < 2 / Av c p β := div_pos two_pos hA
  linarith

/-- `A(β) ≥ 2` exactly when `2β ≤ c/q²`. -/
lemma Av_ge_two_iff (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    2 ≤ Av c p β ↔ 2 * β ≤ c / qf p β ^ 2 := by
  have hq := qf_ne p β hβ hp0 hp1
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have hw0 : 0 ≤ wv c p β := Real.sqrt_nonneg _
  have hq2 : 0 < qf p β ^ 2 := sq_pos_of_ne_zero hq
  have hA : Av c p β = wv c p β + sg β := rfl
  have h2s : 0 < 2 - sg β := by unfold sg; linarith [hβ.1]
  constructor
  · intro h
    have hw : 2 - sg β ≤ wv c p β := by rw [hA] at h; linarith
    have hs : (2 - sg β) ^ 2 ≤ wv c p β ^ 2 := by
      nlinarith [hw0, hw, sq_nonneg (wv c p β - (2 - sg β))]
    rw [hw2] at hs
    have h4 : (2 - sg β) ^ 2 - sg β ^ 2 = 8 * β := by unfold sg; ring
    have h8 : 8 * β ≤ 4 * (c / qf p β ^ 2) := by
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      linarith
    have hfin : (8 * β) / 4 ≤ (4 * (c / qf p β ^ 2)) / 4 :=
      div_le_div_of_nonneg_right h8 (by norm_num)
    linarith
  · intro h
    have h8 : 8 * β ≤ 4 * (c / qf p β ^ 2) := by
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      linarith
    have hs : (2 - sg β) ^ 2 ≤ wv c p β ^ 2 := by
      have h4 : (2 - sg β) ^ 2 = sg β ^ 2 + 8 * β := by unfold sg; ring
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      rw [h4, hw2, h4c]; linarith
    have hw : 2 - sg β ≤ wv c p β := by
      nlinarith [hw0, h2s, hs, sq_nonneg (wv c p β - (2 - sg β))]
    rw [hA]; linarith


lemma wv_gt_sg (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    sg β < wv c p β := by
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have hw0 : 0 ≤ wv c p β := Real.sqrt_nonneg _
  have hq := qf_ne p β hβ hp0 hp1
  have hlt : sg β ^ 2 < wv c p β ^ 2 := by
    rw [hw2]
    have : 0 < 4 * c / qf p β ^ 2 := div_pos (by linarith) (sq_pos_of_ne_zero hq)
    linarith
  by_contra h
  push_neg at h
  have : wv c p β ^ 2 ≤ sg β ^ 2 := pow_le_pow_left₀ hw0 h 2
  linarith

/-- The defining product identity `A (w - σ) = 4c/q²`. -/
lemma Av_mul (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    Av c p β * (wv c p β - sg β) = 4 * c / qf p β ^ 2 := by
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  unfold Av
  nlinarith [hw2]

/-- `M` at the binding policy equals `p²c/(4k)`. -/
lemma Mf_al_gen (k p c β : ℝ) (hk : 0 < k) (hc : 0 < c)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    Mf k p (al c p β) β = p ^ 2 * c / (4 * k) := by
  have hq := qf_ne p β hβ hp0 hp1
  have hA := Av_pos c p β hc hβ hp0 hp1
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have h1a : 1 - al c p β = 2 / Av c p β := by unfold al; ring
  unfold Mf
  rw [h1a]
  field_simp
  have hAv : al c p β * Av c p β = Av c p β - 2 := by unfold al; field_simp
  have hs : Av c p β - 2 + 4 * β = wv c p β - sg β := by unfold Av sg; ring
  rw [hAv, hs, mul_assoc, Av_mul c p β hc hβ hp0 hp1]
  field_simp [hq]
  norm_num

/-- `W` at the binding policy. -/
lemma Wf_al_gen (k p c β : ℝ) (hk : 0 < k) (hc : 0 < c)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    Wf k p (al c p β) β =
      (p * c / (2 * k)) * (qf p β / (wv c p β - sg β)) := by
  have hq := qf_ne p β hβ hp0 hp1
  have hA := Av_pos c p β hc hβ hp0 hp1
  have hws := wv_gt_sg c p β hc hβ hp0 hp1
  have hne : wv c p β - sg β ≠ 0 := by linarith
  have h1a : 1 - al c p β = 2 / Av c p β := by unfold al; ring
  have hprod := Av_mul c p β hc hβ hp0 hp1
  unfold Wf
  rw [h1a]
  field_simp
  rw [mul_assoc, hprod]
  field_simp [hq]

/-- Sign of `α*(β)` and the affordability threshold. -/
lemma al_nonneg_iff (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ al c p β ↔ 2 * β ≤ c / qf p β ^ 2 := by
  have hA := Av_pos c p β hc hβ hp0 hp1
  constructor
  · intro h
    have h1 : 2 / Av c p β ≤ 1 := by unfold al at h; linarith
    have h2 : 2 ≤ 1 * Av c p β := (div_le_iff₀ hA).1 h1
    have h2' : 2 ≤ Av c p β := by simpa using h2
    exact (Av_ge_two_iff c p β hc hβ hp0 hp1).1 h2'
  · intro h
    have h2 := (Av_ge_two_iff c p β hc hβ hp0 hp1).2 h
    have h1 : 2 / Av c p β ≤ 1 := (div_le_iff₀ hA).2 (by simpa using h2)
    unfold al
    linarith

/-- If `2β = c/q²` then the binding policy has `α = 0`. -/
lemma al_eq_zero (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) (h : 2 * β = c / qf p β ^ 2) :
    al c p β = 0 := by
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have hw0 : 0 ≤ wv c p β := Real.sqrt_nonneg _
  have hsq : wv c p β ^ 2 = (1 + 2 * β) ^ 2 := by
    rw [hw2, show 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) by ring, ← h]
    unfold sg
    ring
  have h1 : 0 < 1 + 2 * β := by linarith [hβ.1]
  have hwval : wv c p β = 1 + 2 * β := by
    nlinarith [hsq, hw0, h1, sq_nonneg (wv c p β - (1 + 2 * β))]
  unfold al Av
  rw [hwval]
  unfold sg
  field_simp
  ring


/-! ## The one-variable welfare profile along the binding curve -/

/-- `H(β) = q/(w-σ)`; the welfare at the binding policy is a positive multiple of it. -/
noncomputable def Hfun (c p β : ℝ) : ℝ := qf p β / (wv c p β - sg β)

/-- Transport a `HasDerivAt` along a pointwise function equality. -/
lemma hd_congr {f g : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) (hfg : ∀ y, g y = f y) :
    HasDerivAt g f' x :=
  h.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

lemma hasDerivAt_qf (p β : ℝ) : HasDerivAt (fun β : ℝ => qf p β) p β := by
  have h : HasDerivAt (fun β : ℝ => 1 - (1 - β) * p) p β := by
    have hd : DifferentiableAt ℝ (fun β : ℝ => 1 - (1 - β) * p) β := by fun_prop
    convert hd.hasDerivAt using 1
    · rfl
    · rfl
    · simp [deriv_const, deriv_mul_const, deriv_id'']
  exact hd_congr h (fun y => by rfl)

lemma hasDerivAt_sg (β : ℝ) : HasDerivAt (fun β : ℝ => sg β) (-2) β := by
  have hd : DifferentiableAt ℝ (fun β : ℝ => sg β) β := by unfold sg; fun_prop
  convert hd.hasDerivAt using 1
  · rfl
  · rfl
  · simp [sg, deriv_sub, deriv_const, deriv_const_mul, deriv_id'']

lemma hasDerivAt_g (c p β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun β : ℝ => sg β ^ 2 + 4 * c / qf p β ^ 2)
      (-4 * sg β - 8 * c * p / qf p β ^ 3) β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hσ2 : HasDerivAt (fun β : ℝ => sg β ^ 2) (2 * sg β * (-2)) β := by
    have h := (hasDerivAt_sg β).pow 2
    have h' := h.congr_deriv
      (show (↑2 * sg β ^ (2 - 1) * -2 : ℝ) = 2 * sg β * (-2) by ring)
    exact hd_congr h' (fun y => by rfl)
  have hq2 : HasDerivAt (fun β : ℝ => qf p β ^ 2) (2 * qf p β * p) β := by
    have h := (hasDerivAt_qf p β).pow 2
    have h' := h.congr_deriv
      (show (↑2 * qf p β ^ (2 - 1) * p : ℝ) = 2 * qf p β * p by ring)
    exact hd_congr h' (fun y => by rfl)
  have hdiv : HasDerivAt (fun β : ℝ => 4 * c / qf p β ^ 2)
      ((0 * qf p β ^ 2 - 4 * c * (2 * qf p β * p)) / (qf p β ^ 2) ^ 2) β := by
    have h := (hasDerivAt_const β (4 * c)).div hq2 (pow_ne_zero 2 hq)
    exact hd_congr h (fun y => by rfl)
  have hsum := hσ2.add hdiv
  have hsum' := hd_congr hsum (fun y => by rfl)
  refine hsum'.congr_deriv ?_
  field_simp [hq]
  ring

lemma hasDerivAt_wv (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun β : ℝ => wv c p β)
      ((-2 * sg β - 4 * c * p / qf p β ^ 3) / wv c p β) β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hpos : 0 < sg β ^ 2 + 4 * c / qf p β ^ 2 := by
    have : 0 < 4 * c / qf p β ^ 2 := div_pos (by linarith) (sq_pos_of_ne_zero hq)
    linarith [sq_nonneg (sg β)]
  have hg := hasDerivAt_g c p β hβ hp0 hp1
  have hs := hg.sqrt (ne_of_gt hpos)
  have hw := hd_congr hs (fun y => by rfl)
  have hwv0 : wv c p β ≠ 0 := by
    have : 0 < Real.sqrt (sg β ^ 2 + 4 * c / qf p β ^ 2) := Real.sqrt_pos.2 hpos
    simpa [wv] using this.ne'
  refine hw.congr_deriv ?_
  unfold wv
  field_simp [hq]
  ring

/-- The algebraic identity behind the derivative of `H`. -/
lemma derivH_alg {p Q S W c : ℝ} (hQ : Q ≠ 0) (hW : W ≠ 0) (hD : W - S ≠ 0)
    (hQS : 2 * Q = 2 - p - p * S)
    (h4c : 4 * c = Q ^ 2 * (W ^ 2 - S ^ 2)) :
    (p * (W - S) - Q * ((-2 * S - 4 * c * p / Q ^ 3) / W + 2)) / (W - S) ^ 2
      = (2 * p * (W + S) - (2 - p)) / (W * (W - S)) := by
  have hc' : c = Q ^ 2 * (W ^ 2 - S ^ 2) / 4 := by linarith
  have hQ' : Q = (2 - p - p * S) / 2 := by linarith
  have h2 : 2 - p - p * S ≠ 0 := by
    intro h
    apply hQ
    rw [hQ', h]
    ring
  rw [hc', hQ']
  field_simp [hQ, hW, hD, h2]
  ring

lemma hasDerivAt_H (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun β : ℝ => Hfun c p β)
      ((2 * p * (wv c p β + sg β) - (2 - p)) / (wv c p β * (wv c p β - sg β))) β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hws := wv_gt_sg c p β hc hβ hp0 hp1
  have hne : wv c p β - sg β ≠ 0 := (sub_pos.2 hws).ne'
  have hwvpos : 0 < sg β ^ 2 + 4 * c / qf p β ^ 2 := by
    have : 0 < 4 * c / qf p β ^ 2 := div_pos (by linarith) (sq_pos_of_ne_zero hq)
    linarith [sq_nonneg (sg β)]
  have hwv0 : wv c p β ≠ 0 := by
    have : 0 < Real.sqrt (sg β ^ 2 + 4 * c / qf p β ^ 2) := Real.sqrt_pos.2 hwvpos
    simpa [wv] using this.ne'
  have hwv := hasDerivAt_wv c p β hc hβ hp0 hp1
  have hσ := hasDerivAt_sg β
  have hq' := hasDerivAt_qf p β
  have hsub := hwv.sub hσ
  have hdiv := hq'.div hsub hne
  have hd := hd_congr hdiv (fun y => by rfl)
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  refine hd.congr_deriv ?_
  set W := wv c p β with hWdef
  set Q := qf p β with hQdef
  set S := sg β with hSdef
  have hW2 : W ^ 2 = S ^ 2 + 4 * c / Q ^ 2 := by
    rw [hWdef, hQdef, hSdef]; exact hw2
  have hQS : 2 * Q = 2 - p - p * S := by
    rw [hQdef, hSdef]; unfold qf sg; ring
  have hQne : Q ≠ 0 := by rw [hQdef]; exact hq
  have hWne : W ≠ 0 := by rw [hWdef]; exact hwv0
  have hDne : W - S ≠ 0 := by rw [hWdef, hSdef]; exact hne
  have h4c : 4 * c = Q ^ 2 * (W ^ 2 - S ^ 2) := by
    have h := hW2
    field_simp [hQne] at h
    linarith
  simp only [Pi.sub_apply, sub_neg_eq_add]
  exact derivH_alg hQne hWne hDne hQS h4c

/-- Relating the derivative numerator to the sign of `(5-α)p - 2(1-α)` at `α*(β)`. -/
lemma key_sign (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    2 * p * (wv c p β + sg β) - (2 - p) =
      Av c p β * ((5 - al c p β) * p - 2 * (1 - al c p β)) / 2 := by
  have hA := Av_pos c p β hc hβ hp0 hp1
  have hAne : wv c p β + sg β ≠ 0 := by simpa [Av] using hA.ne'
  unfold al Av
  field_simp [hAne]
  ring

/-! ## The strict affordability threshold and the curve `α*(β)` -/

/-- `c = 4Bk/p²`. -/
noncomputable def cb (k p B : ℝ) : ℝ := 4 * B * k / p ^ 2

lemma cb_pos (k p B : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) : 0 < cb k p B := by
  unfold cb; positivity

lemma Av_gt_two_iff (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    2 < Av c p β ↔ 2 * β < c / qf p β ^ 2 := by
  have hq := qf_ne p β hβ hp0 hp1
  have hw2 := wv_sq c p β hc.le hβ hp0 hp1
  have hw0 : 0 ≤ wv c p β := Real.sqrt_nonneg _
  have hq2 : 0 < qf p β ^ 2 := sq_pos_of_ne_zero hq
  have hA : Av c p β = wv c p β + sg β := rfl
  have h2s : 0 < 2 - sg β := by unfold sg; linarith [hβ.1]
  constructor
  · intro h
    have hw : 2 - sg β < wv c p β := by rw [hA] at h; linarith
    have hs : (2 - sg β) ^ 2 < wv c p β ^ 2 := by
      nlinarith [hw0, hw, sq_nonneg (wv c p β - (2 - sg β))]
    rw [hw2] at hs
    have h4 : (2 - sg β) ^ 2 - sg β ^ 2 = 8 * β := by unfold sg; ring
    have h8 : 8 * β < 4 * (c / qf p β ^ 2) := by
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      linarith
    have hfin : (8 * β) / 4 < (4 * (c / qf p β ^ 2)) / 4 :=
      div_lt_div_of_pos_right h8 (by norm_num)
    linarith
  · intro h
    have h8 : 8 * β < 4 * (c / qf p β ^ 2) := by
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      linarith
    have hs : (2 - sg β) ^ 2 < wv c p β ^ 2 := by
      have h4 : (2 - sg β) ^ 2 = sg β ^ 2 + 8 * β := by unfold sg; ring
      have h4c : 4 * c / qf p β ^ 2 = 4 * (c / qf p β ^ 2) := by ring
      rw [h4, hw2, h4c]; linarith
    have hw : 2 - sg β < wv c p β := by
      nlinarith [hw0, h2s, hs, sq_nonneg (wv c p β - (2 - sg β))]
    rw [hA]; linarith

lemma al_pos_iff (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < al c p β ↔ 2 * β < c / qf p β ^ 2 := by
  have hA := Av_pos c p β hc hβ hp0 hp1
  constructor
  · intro h
    have h1 : 2 / Av c p β < 1 := by unfold al at h; linarith
    have h2 : 2 < Av c p β := (div_lt_one hA).1 h1
    exact (Av_gt_two_iff c p β hc hβ hp0 hp1).1 h2
  · intro h
    have h2 := (Av_gt_two_iff c p β hc hβ hp0 hp1).2 h
    have h1 : 2 / Av c p β < 1 := (div_lt_one hA).2 h2
    unfold al
    linarith

lemma Mf_strictMono_alpha (k p β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    StrictMonoOn (fun α : ℝ => Mf k p α β) (Set.Ico (0 : ℝ) 1) := by
  have h := (reduced_monotone k p hk hp0 hp1).2.2.1 β hβ
  simpa [Mf, qf] using h

lemma Mf_strictMono_beta (k p α : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    StrictMonoOn (fun β : ℝ => Mf k p α β) (Set.Ico (0 : ℝ) 1) := by
  have h := (reduced_monotone k p hk hp0 hp1).2.2.2 α hα
  simpa [Mf, qf] using h

lemma Wf_strictMono_alpha (k p β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    StrictMonoOn (fun α : ℝ => Wf k p α β) (Set.Ico (0 : ℝ) 1) := by
  have h := (reduced_monotone k p hk hp0 hp1).1 β hβ
  simpa [Wf, qf] using h

lemma Mf_zero_eq (k p β : ℝ) :
    Mf k p 0 β = β * p ^ 2 * qf p β ^ 2 / (2 * k) := by
  unfold Mf
  ring

lemma two_mul_eq_cb_of_Mf0 (k p B β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : Mf k p 0 β = B) :
    2 * β = cb k p B / qf p β ^ 2 := by
  have hq := qf_ne p β hβ hp0 hp1
  have hq2 : 0 < qf p β ^ 2 := sq_pos_of_ne_zero hq
  have hp2 : 0 < p ^ 2 := pow_pos hp0 2
  rw [Mf_zero_eq] at h
  have h2 : β * p ^ 2 * qf p β ^ 2 = B * (2 * k) := by
    have := (div_eq_iff (by positivity : (0:ℝ) < 2 * k).ne').1 h
    linarith
  unfold cb
  field_simp [hp2.ne', hq2.ne']
  nlinarith [h2]

lemma Mf_cb (k p B β : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    Mf k p (al (cb k p B) p β) β = B := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have h := Mf_al_gen k p (cb k p B) β hk hc hβ hp0 hp1
  rw [h]
  unfold cb
  field_simp [hp0.ne']

lemma Wf_cb (k p B β : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    Wf k p (al (cb k p B) p β) β = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have h := Wf_al_gen k p (cb k p B) β hk hc hβ hp0 hp1
  simpa [Hfun] using h

lemma al_nonneg_of_Mf0 (k p B β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : Mf k p 0 β ≤ B) :
    0 ≤ al (cb k p B) p β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hq2 : 0 < qf p β ^ 2 := sq_pos_of_ne_zero hq
  have hp2 : 0 < p ^ 2 := pow_pos hp0 2
  rw [al_nonneg_iff (cb k p B) p β (cb_pos k p B hk hB hp0) hβ hp0 hp1]
  rw [Mf_zero_eq] at h
  have h2 : β * p ^ 2 * qf p β ^ 2 ≤ B * (2 * k) := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * k)).1 h
    linarith
  unfold cb
  rw [le_div_iff₀ hq2, le_div_iff₀ hp2]
  nlinarith [h2]

lemma al_pos_of_Mf0_lt (k p B β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : Mf k p 0 β < B) :
    0 < al (cb k p B) p β := by
  have hq := qf_ne p β hβ hp0 hp1
  have hq2 : 0 < qf p β ^ 2 := sq_pos_of_ne_zero hq
  have hp2 : 0 < p ^ 2 := pow_pos hp0 2
  rw [al_pos_iff (cb k p B) p β (cb_pos k p B hk hB hp0) hβ hp0 hp1]
  rw [Mf_zero_eq] at h
  have h2 : β * p ^ 2 * qf p β ^ 2 < B * (2 * k) := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * k)).1 h
    linarith
  unfold cb
  rw [lt_div_iff₀ hq2, lt_div_iff₀ hp2]
  nlinarith [h2]

lemma feasible_le_al (k p B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) (hM : Mf k p α β ≤ B) :
    α ≤ al (cb k p B) p β := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have hα := hpol.1
  have hβ := hpol.2
  have hM0 : Mf k p 0 β ≤ B := by
    have hmono := Mf_strictMono_alpha k p β hk hp0 hp1 hβ
    have h0 : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
    have := hmono.monotoneOn h0 hα hα.1
    linarith
  have hal0 : 0 ≤ al (cb k p B) p β := al_nonneg_of_Mf0 k p B β hk hB hp0 hp1 hβ hM0
  have hal1 : al (cb k p B) p β < 1 := al_lt_one (cb k p B) p β hc hβ hp0 hp1
  have halm : al (cb k p B) p β ∈ Set.Ico (0:ℝ) 1 := ⟨hal0, hal1⟩
  by_contra h
  push_neg at h
  have hmono := Mf_strictMono_alpha k p β hk hp0 hp1 hβ
  have hlt := hmono halm hα h
  have heq : Mf k p (al (cb k p B) p β) β = B := Mf_cb k p B β hk hB hp0 hp1 hβ
  linarith [hlt, hM, heq]

/-! ## Continuity in the subsidy and the binding budget -/

lemma Mf_continuousAt_alpha (k p β a : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (ha1 : a < 1) :
    ContinuousAt (fun x : ℝ => Mf k p x β) a := by
  have h1apos : 0 < 1 - a := by linarith
  have hd1 : 4 * (1 - a) ^ 2 * k ≠ 0 := by
    have : 0 < 4 * (1 - a) ^ 2 * k := by
      have := sq_pos_of_ne_zero h1apos.ne'
      nlinarith
    exact this.ne'
  have hd2 : 2 * (1 - a) * k ≠ 0 := by
    have : 0 < 2 * (1 - a) * k := by nlinarith
    exact this.ne'
  have h1 : ContinuousAt (fun x : ℝ => x * p ^ 2 * qf p β ^ 2 / (4 * (1 - x) ^ 2 * k)) a :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hd1
  have h2 : ContinuousAt (fun x : ℝ => β * p ^ 2 * qf p β ^ 2 / (2 * (1 - x) * k)) a :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hd2
  have hfun : (fun x : ℝ => Mf k p x β) =
      (fun x : ℝ => x * p ^ 2 * qf p β ^ 2 / (4 * (1 - x) ^ 2 * k)) +
      (fun x : ℝ => β * p ^ 2 * qf p β ^ 2 / (2 * (1 - x) * k)) := by
    funext x
    simp [Mf]
  rw [hfun]
  exact h1.add h2

/-- Part (1): at an optimal policy the budget is exactly exhausted (in reduced form). -/
lemma optimal_Mf_eq_B (k p B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hopt : IsOptimal k p B α β) :
    Mf k p α β = B := by
  obtain ⟨hpol, hM, hWmax⟩ := (isOptimal_iff k p B α β hk hp0 hp1).1 hopt
  have hα := hpol.1
  have hβ := hpol.2
  refine le_antisymm hM ?_
  by_contra h
  have hlt : Mf k p α β < B := not_le.1 h
  have hcont := Mf_continuousAt_alpha k p β α hk hp0 hp1 hα.2
  have hmem1 : ∀ᶠ a in nhds α, a < 1 :=
    (isOpen_Iio (a := (1:ℝ))).mem_nhds hα.2
  have hev1 : ∀ᶠ a in nhdsWithin α (Set.Ioi α), a < 1 :=
    hmem1.filter_mono nhdsWithin_le_nhds
  have hmem2 : ∀ᶠ a in nhds α, Mf k p a β < B :=
    hcont.eventually_mem (isOpen_Iio.mem_nhds hlt)
  have hev2 : ∀ᶠ a in nhdsWithin α (Set.Ioi α), Mf k p a β < B :=
    hmem2.filter_mono nhdsWithin_le_nhds
  obtain ⟨a', ⟨ha'1, ha'B⟩, ha'α⟩ :=
    ((hev1.and hev2).and self_mem_nhdsWithin).exists
  have ha'0 : 0 ≤ a' := le_trans hα.1 (le_of_lt ha'α)
  have hpol' : RareDisease.Endogenous.IsPolicy a' β :=
    ⟨⟨ha'0, ha'1⟩, hβ⟩
  have hWle := hWmax a' β hpol' (le_of_lt ha'B)
  have hmono := Wf_strictMono_alpha k p β hk hp0 hp1 hβ
  have hltW : Wf k p α β < Wf k p a' β := hmono hα ⟨ha'0, ha'1⟩ ha'α
  linarith

/-- At `α_max` the budget is exactly exhausted. -/
lemma a_bind (k p B a : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (ha : IsAlphaMax k p B a) :
    Mf k p a 0 = B := by
  obtain ⟨hamem, he, hbr, hspend⟩ := ha.1
  have hpol0 : RareDisease.Endogenous.IsPolicy a 0 :=
    ⟨hamem, ⟨le_refl 0, zero_lt_one⟩⟩
  have hM : Mf k p a 0 ≤ B := by
    have hred := reduced_problem k p a 0 hk hp0 hp1 hpol0 he hbr
    have hsp := hspend
    rw [hred.2] at hsp
    simpa [Mf, qf] using hsp
  refine le_antisymm hM ?_
  by_contra h
  have hlt : Mf k p a 0 < B := not_le.1 h
  have hcont := Mf_continuousAt_alpha k p 0 a hk hp0 hp1 hamem.2
  have hmem1 : ∀ᶠ x in nhds a, x < 1 :=
    (isOpen_Iio (a := (1:ℝ))).mem_nhds hamem.2
  have hev1 : ∀ᶠ x in nhdsWithin a (Set.Ioi a), x < 1 :=
    hmem1.filter_mono nhdsWithin_le_nhds
  have hmem2 : ∀ᶠ x in nhds a, Mf k p x 0 < B :=
    hcont.eventually_mem (isOpen_Iio.mem_nhds hlt)
  have hev2 : ∀ᶠ x in nhdsWithin a (Set.Ioi a), Mf k p x 0 < B :=
    hmem2.filter_mono nhdsWithin_le_nhds
  obtain ⟨a', ⟨ha'1, ha'B⟩, ha'a⟩ :=
    ((hev1.and hev2).and self_mem_nhdsWithin).exists
  have ha'0 : 0 ≤ a' := le_trans hamem.1 (le_of_lt ha'a)
  have hpol' : RareDisease.Endogenous.IsPolicy a' 0 :=
    ⟨⟨ha'0, ha'1⟩, ⟨le_refl 0, zero_lt_one⟩⟩
  have hbr' : p * qf p 0 / (2 * (1 - a') * k) ∈ BR k p a' 0 := by
    rw [br_eq k p a' 0 hk hp0 hp1 hpol']
    simp
  have hsp' : spend k p a' 0 (p * qf p 0 / (2 * (1 - a') * k)) ≤ B := by
    have hred := reduced_problem k p a' 0 hk hp0 hp1 hpol' _ hbr'
    rw [hred.2]; simpa [Mf, qf] using le_of_lt ha'B
  have ha'S : a' ∈ {α : ℝ | α ∈ Set.Ico (0:ℝ) 1 ∧
      ∃ e ∈ BR k p α 0, spend k p α 0 e ≤ B} :=
    ⟨⟨ha'0, ha'1⟩, _, hbr', hsp'⟩
  have := ha.2 ha'S
  linarith

/-- `α*(0) = α_max`. -/
lemma al_zero_eq_a (k p B a : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (ha : IsAlphaMax k p B a) :
    al (cb k p B) p 0 = a := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have hβ0 : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
  have hM_a : Mf k p a 0 = B := a_bind k p B a hk hB hp0 hp1 ha
  have hM_al : Mf k p (al (cb k p B) p 0) 0 = B := Mf_cb k p B 0 hk hB hp0 hp1 hβ0
  have hal0 : 0 ≤ al (cb k p B) p 0 := by
    have h : Mf k p 0 0 ≤ B := by
      have hz : Mf k p 0 0 = 0 := by rw [Mf_zero_eq]; ring
      rw [hz]; exact hB.le
    exact al_nonneg_of_Mf0 k p B 0 hk hB hp0 hp1 hβ0 h
  have hal1 : al (cb k p B) p 0 < 1 := al_lt_one (cb k p B) p 0 hc hβ0 hp0 hp1
  have halmem : al (cb k p B) p 0 ∈ Set.Ico (0:ℝ) 1 := ⟨hal0, hal1⟩
  have hamem : a ∈ Set.Ico (0:ℝ) 1 := ha.1.1
  have hmono := Mf_strictMono_alpha k p 0 hk hp0 hp1 hβ0
  rcases lt_trichotomy a (al (cb k p B) p 0) with h | h | h
  · have := hmono hamem halmem h; linarith
  · exact h.symm
  · have := hmono halmem hamem h; linarith

/-! ## Existence of the patient-only endpoint `β₁` -/

lemma exists_beta1 (k p B : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hBlt : B < p ^ 2 / (2 * k)) :
    ∃ β₁ : ℝ, β₁ ∈ Set.Ioo (0:ℝ) 1 ∧ Mf k p 0 β₁ = B := by
  set g : ℝ → ℝ := fun β => Mf k p 0 β with hg
  have hgfun : g = fun β : ℝ => β * p ^ 2 * qf p β ^ 2 * (2 * k)⁻¹ := by
    funext β
    show Mf k p 0 β = β * p ^ 2 * qf p β ^ 2 * (2 * k)⁻¹
    rw [Mf_zero_eq]
    ring
  have hg0 : g 0 = 0 := by
    rw [hgfun]; simp
  have hg1 : g 1 = p ^ 2 / (2 * k) := by
    rw [hgfun]
    unfold qf
    field_simp
    ring
  have hcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := by
    rw [hgfun]
    simp only [qf]
    fun_prop
  have hmem : B ∈ Set.Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨hB.le, hBlt.le⟩
  obtain ⟨x, hx, hxB⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hcont hmem
  refine ⟨x, ⟨?_, ?_⟩, hxB⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      rw [hg0] at hxB
      linarith
    exact lt_of_le_of_ne hx.1 (Ne.symm hx0)
  · have hx1 : x ≠ 1 := by
      rintro rfl
      rw [hg1] at hxB
      linarith
    exact lt_of_le_of_ne hx.2 hx1

lemma beta1_unique (k p B β β' : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hβ : β ∈ Set.Ico (0:ℝ) 1) (hβ' : β' ∈ Set.Ico (0:ℝ) 1)
    (h : Mf k p 0 β = B) (h' : Mf k p 0 β' = B) : β = β' := by
  have h0 : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
  have hmono := Mf_strictMono_beta k p 0 hk hp0 hp1 h0
  rcases lt_trichotomy β β' with hlt | heq | hgt
  · have := hmono hβ hβ' hlt; linarith
  · exact heq
  · have := hmono hβ' hβ hgt; linarith

/-! ## Monotonicity of the welfare profile along the binding curve -/

lemma wv_pos (c p β : ℝ) (hc : 0 < c) (hβ : β ∈ Set.Ico (0:ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < wv c p β := by
  have hq := qf_ne p β hβ hp0 hp1
  unfold wv
  exact Real.sqrt_pos.2 (by
    have : 0 < 4 * c / qf p β ^ 2 := div_pos (by linarith) (sq_pos_of_ne_zero hq)
    linarith [sq_nonneg (sg β)])

lemma H_strictMono_Icc (c p b : ℝ) (hc : 0 < c) (hb0 : 0 < b) (hb1 : b < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hp25 : 2 / 5 < p)
    (hal : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 ≤ al c p x) :
    StrictMonoOn (fun β => Hfun c p β) (Set.Icc (0:ℝ) b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (D := Set.Icc (0:ℝ) b)
    (f := fun β => Hfun c p β)
    (f' := fun x => (2 * p * (wv c p x + sg x) - (2 - p)) /
      (wv c p x * (wv c p x - sg x))) (convex_Icc 0 b) ?_ ?_ ?_
  · intro x hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hb1⟩
    exact ((hasDerivAt_H c p x hc hxI hp0 hp1).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hb1⟩
    exact (hasDerivAt_H c p x hc hxI hp0 hp1).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hb1⟩
    have hA := Av_pos c p x hc hxI hp0 hp1
    have hws := wv_gt_sg c p x hc hxI hp0 hp1
    have hden : 0 < wv c p x * (wv c p x - sg x) :=
      mul_pos (wv_pos c p x hc hxI hp0 hp1) (by linarith)
    have hkey := key_sign c p x hc hxI hp0 hp1
    have hE : 0 < (5 - al c p x) * p - 2 * (1 - al c p x) := by
      have h1 : 0 ≤ al c p x := hal x hx
      have h2 : 0 ≤ 2 - p := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hnum : 0 < 2 * p * (wv c p x + sg x) - (2 - p) := by
      rw [hkey]
      exact div_pos (mul_pos hA hE) (by norm_num)
    exact div_pos hnum hden

lemma H_strictAnti_Icc (c p a b : ℝ) (hc : 0 < c) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hEa : (5 - a) * p - 2 * (1 - a) ≤ 0)
    (hal : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 ≤ al c p x ∧ al c p x < a) :
    StrictAntiOn (fun β => Hfun c p β) (Set.Icc (0:ℝ) b) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (D := Set.Icc (0:ℝ) b)
    (f := fun β => Hfun c p β)
    (f' := fun x => (2 * p * (wv c p x + sg x) - (2 - p)) /
      (wv c p x * (wv c p x - sg x))) (convex_Icc 0 b) ?_ ?_ ?_
  · intro x hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hb1⟩
    exact ((hasDerivAt_H c p x hc hxI hp0 hp1).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hb1⟩
    exact (hasDerivAt_H c p x hc hxI hp0 hp1).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hb1⟩
    have hA := Av_pos c p x hc hxI hp0 hp1
    have hws := wv_gt_sg c p x hc hxI hp0 hp1
    have hden : 0 < wv c p x * (wv c p x - sg x) :=
      mul_pos (wv_pos c p x hc hxI hp0 hp1) (by linarith)
    have hkey := key_sign c p x hc hxI hp0 hp1
    have hlt := (hal x hx).2
    have hE : (5 - al c p x) * p - 2 * (1 - al c p x) < 0 := by
      have h2 : 0 < 2 - p := by linarith
      have hEq : (5 - al c p x) * p - 2 * (1 - al c p x)
          = ((5 - a) * p - 2 * (1 - a)) - (a - al c p x) * (2 - p) := by ring
      rw [hEq]
      have hpos : 0 < (a - al c p x) * (2 - p) := mul_pos (by linarith) h2
      linarith
    have hnum : 2 * p * (wv c p x + sg x) - (2 - p) < 0 := by
      rw [hkey]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA hE) (by norm_num)
    exact div_neg_of_neg_of_pos hnum hden

/-! ## Auxiliary facts for the two price regimes -/

lemma al_nonneg_of_lt_beta1 (k p B β₁ x : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hβ₁ : β₁ ∈ Set.Ico (0:ℝ) 1)
    (hβ₁eq : Mf k p 0 β₁ = B) (hx : x ∈ Set.Ioo (0:ℝ) β₁) :
    0 ≤ al (cb k p B) p x := by
  have h0I : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
  have hxmem : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hβ₁.2⟩
  have hlt0 : Mf k p 0 x < Mf k p 0 β₁ :=
    (Mf_strictMono_beta k p 0 hk hp0 hp1 h0I) hxmem hβ₁ hx.2
  rw [hβ₁eq] at hlt0
  exact al_nonneg_of_Mf0 k p B x hk hB hp0 hp1 hxmem (le_of_lt hlt0)

lemma al_lt_a_of_feas (k p B a β x : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (ha : IsAlphaMax k p B a)
    (hβ : β ∈ Set.Ico (0:ℝ) 1) (hM0 : Mf k p 0 β ≤ B)
    (hx : x ∈ Set.Ioo (0:ℝ) β) :
    0 ≤ al (cb k p B) p x ∧ al (cb k p B) p x < a := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have h0I : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
  have hxmem : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx.1, lt_trans hx.2 hβ.2⟩
  have hlt0 : Mf k p 0 x < Mf k p 0 β :=
    (Mf_strictMono_beta k p 0 hk hp0 hp1 h0I) hxmem hβ hx.2
  have hMx : Mf k p 0 x < B := lt_of_lt_of_le hlt0 hM0
  have halx0 : 0 ≤ al (cb k p B) p x :=
    le_of_lt (al_pos_of_Mf0_lt k p B x hk hB hp0 hp1 hxmem hMx)
  have halx1 : al (cb k p B) p x < 1 := al_lt_one (cb k p B) p x hc hxmem hp0 hp1
  have halxa : al (cb k p B) p x < a := by
    by_contra h
    push_neg at h
    have hamem : a ∈ Set.Ico (0:ℝ) 1 := ha.1.1
    have hle1 : Mf k p a x ≤ Mf k p (al (cb k p B) p x) x :=
      (Mf_strictMono_alpha k p x hk hp0 hp1 hxmem).monotoneOn hamem ⟨halx0, halx1⟩ h
    have heq : Mf k p (al (cb k p B) p x) x = B := Mf_cb k p B x hk hB hp0 hp1 hxmem
    have hgt : B < Mf k p a x := by
      have hmono := Mf_strictMono_beta k p a hk hp0 hp1 hamem
      have h := hmono h0I hxmem hx.1
      change Mf k p a 0 < Mf k p a x at h
      rw [a_bind k p B a hk hB hp0 hp1 ha] at h
      exact h
    linarith
  exact ⟨halx0, halxa⟩

lemma E_a_nonpos (p a : ℝ) (hp0 : 0 < p) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hp_low : p ≤ 2 * (1 - a) / 5) :
    (5 - a) * p - 2 * (1 - a) ≤ 0 := by
  have h5 : 0 < 5 - a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have h := mul_le_mul_of_nonneg_left hp_low (le_of_lt h5)
  nlinarith [h]

lemma al_zero_closed (k p B : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1) :
    al (cb k p B) p 0 =
      (8 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2
          - (p - p ^ 2) * Real.sqrt (16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2)) /
        (8 * B * k) := by
  set E : ℝ := p * (1 - p) with hE
  set D : ℝ := 16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2 with hD
  set S : ℝ := Real.sqrt D with hS
  have hEpos : 0 < E := by rw [hE]; exact mul_pos hp0 (by linarith)
  have hEnn : 0 ≤ E := hEpos.le
  have hDeq : D = 16 * B * k + E ^ 2 := by rw [hD, hE]; ring
  have hDnn : 0 ≤ D := by rw [hDeq]; positivity
  have hSsq : S ^ 2 = D := by rw [hS]; exact Real.sq_sqrt hDnn
  have hSnn : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  have hsqrtDsq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hDnn
  have h1p : (0:ℝ) < 1 - p := by linarith
  have hq0 : qf p 0 = 1 - p := by unfold qf; ring
  have hw2 : wv (cb k p B) p 0 ^ 2 = (S / E) ^ 2 := by
    have hβ0 : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
    rw [wv_sq (cb k p B) p 0 (cb_pos k p B hk hB hp0).le hβ0 hp0 hp1, hq0]
    rw [hS, div_pow, hsqrtDsq]
    unfold sg
    rw [hDeq]
    unfold cb
    rw [hE]
    field_simp [hp0.ne', h1p.ne']
    ring
  have hw : wv (cb k p B) p 0 = S / E := by
    have hw0 : 0 ≤ wv (cb k p B) p 0 := Real.sqrt_nonneg _
    have hR : 0 ≤ S / E := div_nonneg hSnn hEnn
    nlinarith [hw2, hw0, hR, sq_nonneg (wv (cb k p B) p 0 - S / E)]
  have hA0 : Av (cb k p B) p 0 = S / E + 1 := by
    unfold Av
    rw [hw]
    unfold sg
    norm_num
  have hden : S / E + 1 ≠ 0 := by
    have : 0 ≤ S / E := div_nonneg hSnn hEnn
    have : 0 < S / E + 1 := by linarith
    exact this.ne'
  have halw : al (cb k p B) p 0 = (S / E - 1) / (S / E + 1) := by
    unfold al
    rw [hA0]
    field_simp [hden]
    ring
  have hden2 : S + E ≠ 0 := by
    have : 0 < S + E := by linarith
    exact this.ne'
  have hSE : (S / E - 1) / (S / E + 1) = (S - E) / (S + E) := by
    field_simp [hEpos.ne', hden2]
  have hSminus : 0 < S - E := by
    nlinarith [hSsq, hSnn, hEnn, hEpos, hDeq, hB, hk]
  have hrat : (S - E) / (S + E) = (D + E ^ 2 - 2 * E * S) / (D - E ^ 2) := by
    have h1 : D - E ^ 2 = (S - E) * (S + E) := by nlinarith [hSsq]
    have h2 : D + E ^ 2 - 2 * E * S = (S - E) ^ 2 := by nlinarith [hSsq]
    rw [h1, h2]
    field_simp [hSminus.ne', hden2]
  have hfinal : (D + E ^ 2 - 2 * E * S) / (D - E ^ 2)
      = (8 * B * k + E ^ 2 - E * S) / (8 * B * k) := by
    have hsub : D - E ^ 2 = 16 * B * k := by rw [hDeq]; ring
    have hadd : D + E ^ 2 = 16 * B * k + 2 * E ^ 2 := by rw [hDeq]; ring
    rw [hsub, hadd]
    have h16 : (0:ℝ) < 16 * B * k := by positivity
    have h8 : (0:ℝ) < 8 * B * k := by positivity
    field_simp [h16.ne', h8.ne']
    ring
  rw [halw, hSE, hrat, hfinal]
  rw [show E ^ 2 = p ^ 4 - 2 * p ^ 3 + p ^ 2 by rw [hE]; ring]
  rw [show E = p - p ^ 2 by rw [hE]; ring]
  rw [show S = Real.sqrt (16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2) by rw [hS, hD]]
  ring

/-- The optimal subsidy `α` is the binding value `α*(β)`. -/
lemma optimal_eq_al (k p B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp0 : 0 < p) (hp1 : p < 1) (hopt : IsOptimal k p B α β) :
    α = al (cb k p B) p β := by
  have hM := optimal_Mf_eq_B k p B α β hk hB hp0 hp1 hopt
  have hpol := hopt.1
  have hα : α ∈ Set.Ico (0:ℝ) 1 := hpol.1
  have hβ : β ∈ Set.Ico (0:ℝ) 1 := hpol.2
  have hle := feasible_le_al k p B α β hk hB hp0 hp1 hpol hM.le
  have hM0 : Mf k p 0 β ≤ B := by
    have := (Mf_strictMono_alpha k p β hk hp0 hp1 hβ).monotoneOn
      (show (0:ℝ) ∈ Set.Ico (0:ℝ) 1 from ⟨le_refl 0, zero_lt_one⟩) hα hα.1
    linarith
  have hal0 := al_nonneg_of_Mf0 k p B β hk hB hp0 hp1 hβ hM0
  have hal1 := al_lt_one (cb k p B) p β (cb_pos k p B hk hB hp0) hβ hp0 hp1
  have hmono := Mf_strictMono_alpha k p β hk hp0 hp1 hβ
  refine le_antisymm hle ?_
  by_contra h
  push_neg at h
  have hlt := hmono hα ⟨hal0, hal1⟩ h
  have heq : Mf k p (al (cb k p B) p β) β = B := Mf_cb k p B β hk hB hp0 hp1 hβ
  linarith

/-- Proposition 3, parts (1) and (3). -/
theorem proposition_3 (k B p : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ℝ) (ha : IsAlphaMax k p B a) :
    (∀ α β : ℝ, IsOptimal k p B α β → ∀ e ∈ BR k p α β, spend k p α β e = B) ∧
    (2 / (5 - a) ≤ p → B < p ^ 2 / (2 * k) →
      ∃ β₁ : ℝ, IsOptimal k p B 0 β₁ ∧
        ∀ α β : ℝ, IsOptimal k p B α β → α = 0 ∧ β = β₁) ∧
    (p ≤ 2 * (1 - a) / 5 →
      IsOptimal k p B a 0 ∧
        (∀ α β : ℝ, IsOptimal k p B α β → α = a ∧ β = 0) ∧
        a = (8 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2
              - (p - p ^ 2) * Real.sqrt (16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2)) /
            (8 * B * k)) := by
  have hc : 0 < cb k p B := cb_pos k p B hk hB hp0
  have h0I : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨le_refl 0, zero_lt_one⟩
  have ha0 : 0 ≤ a := ha.1.1.1
  have ha1 : a < 1 := ha.1.1.2
  have hMa0 : Mf k p a 0 = B := a_bind k p B a hk hB hp0 hp1 ha
  have hal0 : al (cb k p B) p 0 = a := al_zero_eq_a k p B a hk hB hp0 hp1 ha
  have hcoef : 0 < p * cb k p B / (2 * k) :=
    div_pos (mul_pos hp0 hc) (by positivity)
  have hW_a0 : Wf k p a 0 = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p 0 := by
    have h := Wf_cb k p B 0 hk hB hp0 hp1 h0I
    rwa [hal0] at h
  refine ⟨?_, ?_, ?_⟩
  · -- (1) binding budget
    intro α β hopt e he
    have hM := optimal_Mf_eq_B k p B α β hk hB hp0 hp1 hopt
    have hpol := hopt.1
    have hred := reduced_problem k p α β hk hp0 hp1 hpol e he
    rw [hred.2]
    simpa [Mf, qf] using hM
  · -- (2) high price: patient-only
    intro hp_high hBlt
    have hapos : 0 < a := by
      rcases ha0.eq_or_lt with h | h
      · exfalso
        have hz : Mf k p 0 0 = 0 := by rw [Mf_zero_eq]; ring
        rw [← h, hz] at hMa0
        linarith
      · exact h
    have hp25 : 2 / 5 < p := by
      have h5 : 0 < 5 - a := by linarith
      have h2 : (2:ℝ) / 5 < 2 / (5 - a) := by
        field_simp [h5.ne', (by norm_num : (5:ℝ) ≠ 0)]
        linarith
      linarith
    obtain ⟨β₁, hβ₁mem, hβ₁eq⟩ := exists_beta1 k p B hk hB hp0 hp1 hBlt
    have hβ₁0 : 0 < β₁ := hβ₁mem.1
    have hβ₁1 : β₁ < 1 := hβ₁mem.2
    have hβ₁I : β₁ ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hβ₁0, hβ₁1⟩
    have halβ₁ : al (cb k p B) p β₁ = 0 := by
      refine al_eq_zero (cb k p B) p β₁ hc hβ₁I hp0 hp1 ?_
      exact two_mul_eq_cb_of_Mf0 k p B β₁ hk hB hp0 hp1 hβ₁I hβ₁eq
    have hWβ₁ : Wf k p 0 β₁ = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β₁ := by
      have h := Wf_cb k p B β₁ hk hB hp0 hp1 hβ₁I
      rwa [halβ₁] at h
    have hmono : StrictMonoOn (fun β => Hfun (cb k p B) p β) (Set.Icc (0:ℝ) β₁) :=
      H_strictMono_Icc (cb k p B) p β₁ hc hβ₁0 hβ₁1 hp0 hp1 hp25
        (fun x hx => al_nonneg_of_lt_beta1 k p B β₁ x hk hB hp0 hp1 hβ₁I hβ₁eq hx)
    have hM0_le : ∀ β ∈ Set.Ico (0:ℝ) 1, Mf k p 0 β ≤ B → Mf k p 0 β ≤ Mf k p 0 β₁ := by
      intro β hβ hMβ
      rw [hβ₁eq]; exact hMβ
    have hbeq : ∀ β ∈ Set.Ico (0:ℝ) 1, Mf k p 0 β ≤ B → β ≤ β₁ := by
      intro β hβ hMβ
      by_contra h
      push_neg at h
      have := (Mf_strictMono_beta k p 0 hk hp0 hp1 h0I) hβ₁I hβ h
      linarith [hM0_le β hβ hMβ, hβ₁eq]
    have hoptβ₁ : IsOptimal k p B 0 β₁ := by
      rw [isOptimal_iff k p B 0 β₁ hk hp0 hp1]
      refine ⟨⟨⟨le_refl 0, zero_lt_one⟩, hβ₁I⟩, ?_, ?_⟩
      · rw [hβ₁eq]
      · intro α' β' hpol' hM'
        have hα' : α' ∈ Set.Ico (0:ℝ) 1 := hpol'.1
        have hβ' : β' ∈ Set.Ico (0:ℝ) 1 := hpol'.2
        have hM0' : Mf k p 0 β' ≤ B := by
          have := (Mf_strictMono_alpha k p β' hk hp0 hp1 hβ').monotoneOn h0I hα' hα'.1
          linarith
        have hβ'le : β' ≤ β₁ := hbeq β' hβ' hM0'
        have hα'le : α' ≤ al (cb k p B) p β' :=
          feasible_le_al k p B α' β' hk hB hp0 hp1 hpol' hM'
        have halmem : al (cb k p B) p β' ∈ Set.Ico (0:ℝ) 1 :=
          ⟨al_nonneg_of_Mf0 k p B β' hk hB hp0 hp1 hβ' hM0',
            al_lt_one (cb k p B) p β' hc hβ' hp0 hp1⟩
        have hWle1 : Wf k p α' β' ≤ Wf k p (al (cb k p B) p β') β' :=
          (Wf_strictMono_alpha k p β' hk hp0 hp1 hβ').monotoneOn hα' halmem hα'le
        have hWcurve : Wf k p (al (cb k p B) p β') β' =
            (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β' :=
          Wf_cb k p B β' hk hB hp0 hp1 hβ'
        have hHle : Hfun (cb k p B) p β' ≤ Hfun (cb k p B) p β₁ :=
          hmono.monotoneOn ⟨hβ'.1, hβ'le⟩ ⟨le_of_lt hβ₁0, le_refl β₁⟩ hβ'le
        calc Wf k p α' β' ≤ Wf k p (al (cb k p B) p β') β' := hWle1
          _ = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β' := hWcurve
          _ ≤ (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β₁ :=
              mul_le_mul_of_nonneg_left hHle hcoef.le
          _ = Wf k p 0 β₁ := hWβ₁.symm
    refine ⟨β₁, hoptβ₁, ?_⟩
    intro α β hopt
    have hM := optimal_Mf_eq_B k p B α β hk hB hp0 hp1 hopt
    have hpol := hopt.1
    have hαeq : α = al (cb k p B) p β := optimal_eq_al k p B α β hk hB hp0 hp1 hopt
    have hα : α ∈ Set.Ico (0:ℝ) 1 := hpol.1
    have hβ : β ∈ Set.Ico (0:ℝ) 1 := hpol.2
    have hM0 : Mf k p 0 β ≤ B := by
      have := (Mf_strictMono_alpha k p β hk hp0 hp1 hβ).monotoneOn h0I hα hα.1
      linarith
    have hβle : β ≤ β₁ := hbeq β hβ hM0
    have hWα : Wf k p α β = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β := by
      rw [hαeq]; exact Wf_cb k p B β hk hB hp0 hp1 hβ
    have hle1 : Wf k p α β ≤ Wf k p 0 β₁ :=
      ((isOptimal_iff k p B 0 β₁ hk hp0 hp1).1 hoptβ₁).2.2 α β hpol (le_of_eq hM)
    have hle2 : Wf k p 0 β₁ ≤ Wf k p α β :=
      ((isOptimal_iff k p B α β hk hp0 hp1).1 hopt).2.2 0 β₁
        ⟨⟨le_refl 0, zero_lt_one⟩, hβ₁I⟩ (le_of_eq hβ₁eq)
    have hWeq : Wf k p α β = Wf k p 0 β₁ := le_antisymm hle1 hle2
    have hHβ : Hfun (cb k p B) p β = Hfun (cb k p B) p β₁ := by
      have hmul : (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β =
          (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β₁ := by
        rw [← hWα, ← hWβ₁]
        exact hWeq
      exact mul_left_cancel₀ hcoef.ne' hmul
    have hβeq : β = β₁ := by
      have hnot : ¬ β < β₁ := by
        intro hlt
        have := hmono ⟨hβ.1, hβle⟩ ⟨le_of_lt hβ₁0, le_refl β₁⟩ hlt
        linarith [hHβ]
      exact le_antisymm hβle (le_of_not_gt hnot)
    refine ⟨?_, hβeq⟩
    rw [hαeq, hβeq, halβ₁]
  · -- (3) low price: manufacturer-only
    intro hp_low
    have hEa : (5 - a) * p - 2 * (1 - a) ≤ 0 := E_a_nonpos p a hp0 ha0 ha1 hp_low
    have hopt_a0 : IsOptimal k p B a 0 := by
      rw [isOptimal_iff k p B a 0 hk hp0 hp1]
      refine ⟨⟨⟨ha0, ha1⟩, ⟨le_refl 0, zero_lt_one⟩⟩, ?_, ?_⟩
      · rw [hMa0]
      · intro α' β' hpol' hM'
        have hα' : α' ∈ Set.Ico (0:ℝ) 1 := hpol'.1
        have hβ' : β' ∈ Set.Ico (0:ℝ) 1 := hpol'.2
        have hM0' : Mf k p 0 β' ≤ B := by
          have := (Mf_strictMono_alpha k p β' hk hp0 hp1 hβ').monotoneOn h0I hα' hα'.1
          linarith
        have hα'le : α' ≤ al (cb k p B) p β' :=
          feasible_le_al k p B α' β' hk hB hp0 hp1 hpol' hM'
        have halmem : al (cb k p B) p β' ∈ Set.Ico (0:ℝ) 1 :=
          ⟨al_nonneg_of_Mf0 k p B β' hk hB hp0 hp1 hβ' hM0',
            al_lt_one (cb k p B) p β' hc hβ' hp0 hp1⟩
        have hWle1 : Wf k p α' β' ≤ Wf k p (al (cb k p B) p β') β' :=
          (Wf_strictMono_alpha k p β' hk hp0 hp1 hβ').monotoneOn hα' halmem hα'le
        have hWcurve : Wf k p (al (cb k p B) p β') β' =
            (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β' :=
          Wf_cb k p B β' hk hB hp0 hp1 hβ'
        rcases hβ'.1.eq_or_lt with h0 | h0
        · have hβ'0 : β' = 0 := h0.symm
          rw [hβ'0]
          have hα'a : α' ≤ a := by
            have h := hα'le
            rw [hβ'0] at h
            rwa [hal0] at h
          have := (Wf_strictMono_alpha k p 0 hk hp0 hp1 h0I).monotoneOn hα' ⟨ha0, ha1⟩ hα'a
          exact this
        · have hanti : StrictAntiOn (fun β => Hfun (cb k p B) p β) (Set.Icc (0:ℝ) β') :=
            H_strictAnti_Icc (cb k p B) p a β' hc ha0 ha1 h0 hβ'.2 hp0 hp1 hEa
              (fun x hx => al_lt_a_of_feas k p B a β' x hk hB hp0 hp1 ha hβ' hM0' hx)
          have hHlt : Hfun (cb k p B) p β' < Hfun (cb k p B) p 0 :=
            hanti ⟨le_refl 0, le_of_lt h0⟩ ⟨le_of_lt h0, le_refl β'⟩ h0
          have hlt : Wf k p α' β' < Wf k p a 0 :=
            calc Wf k p α' β' ≤ Wf k p (al (cb k p B) p β') β' := hWle1
              _ = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β' := hWcurve
              _ < (p * cb k p B / (2 * k)) * Hfun (cb k p B) p 0 :=
                  mul_lt_mul_of_pos_left hHlt hcoef
              _ = Wf k p a 0 := hW_a0.symm
          exact le_of_lt hlt
    refine ⟨hopt_a0, ?_, ?_⟩
    · intro α β hopt
      have hM := optimal_Mf_eq_B k p B α β hk hB hp0 hp1 hopt
      have hpol := hopt.1
      have hαeq : α = al (cb k p B) p β := optimal_eq_al k p B α β hk hB hp0 hp1 hopt
      have hα : α ∈ Set.Ico (0:ℝ) 1 := hpol.1
      have hβ : β ∈ Set.Ico (0:ℝ) 1 := hpol.2
      have hM0 : Mf k p 0 β ≤ B := by
        have := (Mf_strictMono_alpha k p β hk hp0 hp1 hβ).monotoneOn h0I hα hα.1
        linarith
      have hWα : Wf k p α β = (p * cb k p B / (2 * k)) * Hfun (cb k p B) p β := by
        rw [hαeq]; exact Wf_cb k p B β hk hB hp0 hp1 hβ
      have hle1 : Wf k p α β ≤ Wf k p a 0 :=
        ((isOptimal_iff k p B a 0 hk hp0 hp1).1 hopt_a0).2.2 α β hpol (le_of_eq hM)
      have hle2 : Wf k p a 0 ≤ Wf k p α β :=
        ((isOptimal_iff k p B α β hk hp0 hp1).1 hopt).2.2 a 0
          ⟨⟨ha0, ha1⟩, ⟨le_refl 0, zero_lt_one⟩⟩ (le_of_eq hMa0)
      have hWeq : Wf k p α β = Wf k p a 0 := le_antisymm hle1 hle2
      have hβ0 : β = 0 := by
        by_contra h
        have hβpos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm h)
        have hanti : StrictAntiOn (fun β => Hfun (cb k p B) p β) (Set.Icc (0:ℝ) β) :=
          H_strictAnti_Icc (cb k p B) p a β hc ha0 ha1 hβpos hβ.2 hp0 hp1 hEa
            (fun x hx => al_lt_a_of_feas k p B a β x hk hB hp0 hp1 ha hβ hM0 hx)
        have hHlt : Hfun (cb k p B) p β < Hfun (cb k p B) p 0 :=
          hanti ⟨le_refl 0, le_of_lt hβpos⟩ ⟨le_of_lt hβpos, le_refl β⟩ hβpos
        have hWlt : Wf k p α β < Wf k p a 0 := by
          rw [hWα, hW_a0]
          exact mul_lt_mul_of_pos_left hHlt hcoef
        rw [hWeq] at hWlt
        linarith
      refine ⟨?_, hβ0⟩
      rw [hαeq, hβ0, hal0]
    · rw [← hal0]
      exact al_zero_closed k p B hk hB hp0 hp1

end

end DS19B

open RareDisease.ExogOutcome

/-- Proposition 3 in Setting (2B), with the exact live hypotheses and conclusions:
every optimum exhausts the budget; the high-price optimum is unique under
`B < p² / (2k)`; the low-price optimum is unique and has the stated closed form.
Here `a` is `α_max`. -/
theorem solution (k B p : ℝ) (hk : 0 < k) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ℝ) (ha : IsAlphaMax k p B a) :
    (∀ α β : ℝ, IsOptimal k p B α β → ∀ e ∈ BR k p α β, spend k p α β e = B) ∧
    (2 / (5 - a) ≤ p → B < p ^ 2 / (2 * k) →
      ∃ β₁ : ℝ, IsOptimal k p B 0 β₁ ∧
        ∀ α β : ℝ, IsOptimal k p B α β → α = 0 ∧ β = β₁) ∧
    (p ≤ 2 * (1 - a) / 5 →
      IsOptimal k p B a 0 ∧
        (∀ α β : ℝ, IsOptimal k p B α β → α = a ∧ β = 0) ∧
        a = (8 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2
              - (p - p ^ 2) * Real.sqrt (16 * B * k + p ^ 4 - 2 * p ^ 3 + p ^ 2)) / (8 * B * k)) :=
  DS19B.proposition_3 k B p hk hB hp0 hp1 a ha

#check @solution
#print axioms solution
