-- Prove2me | solution 1 for TalagrandConc.Penalties.corollary_2_4_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:43:42.197293+00:00
-- url     : https://prove2.me/submissions/b5706792-381f-483e-95ac-ae088a812fe8

import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory
open scoped ENNReal Classical

namespace TalagrandConc.Penalties

/-! ### The exponential integrand -/

/-- `e^{t z}` for `z : ℝ≥0∞`. -/
noncomputable def ex (t : ℝ) (z : ℝ≥0∞) : ℝ≥0∞ := EReal.exp ((t : EReal) * (z : EReal))

lemma ex_eq (t : ℝ) (ht : 0 ≤ t) (z : ℝ≥0∞) :
    ex t z = EReal.exp (((ENNReal.ofReal t * z : ℝ≥0∞)) : EReal) := by
  unfold ex
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ht]

lemma ex_mono (t : ℝ) (ht : 0 ≤ t) {z₁ z₂ : ℝ≥0∞} (h : z₁ ≤ z₂) : ex t z₁ ≤ ex t z₂ := by
  rw [ex_eq t ht, ex_eq t ht]
  apply EReal.exp_monotone
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact mul_le_mul' le_rfl h

lemma ex_add_const (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : 0 ≤ c) (z : ℝ≥0∞) :
    ex t (ENNReal.ofReal c + z) = ENNReal.ofReal (Real.exp (t * c)) * ex t z := by
  rw [ex_eq t ht, ex_eq t ht, mul_add, ← ENNReal.ofReal_mul ht, EReal.coe_ennreal_add,
    EReal.exp_add, EReal.coe_ennreal_ofReal, max_eq_left (by positivity), EReal.exp_coe]

lemma ex_zero' (t : ℝ) : ex t 0 = 1 := by
  unfold ex
  simp

lemma ex_ofReal (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : 0 ≤ c) :
    ex t (ENNReal.ofReal c) = ENNReal.ofReal (Real.exp (t * c)) := by
  have := ex_add_const t ht c hc 0
  rw [add_zero, ex_zero', mul_one] at this
  exact this

/-! ### The penalized distance and sections -/

def cns {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.cons (α := fun _ => Ω) ω z

@[simp] lemma cns_zero {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) : cns ω z 0 = ω := by
  simp [cns]

@[simp] lemma cns_succ {Ω : Type*} {N : ℕ} (ω : Ω) (z : Fin N → Ω) (j : Fin N) :
    cns ω z j.succ = z j := by
  simp [cns]

def sec {Ω : Type*} {N : ℕ} (ω : Ω) (A : Set (Fin (N + 1) → Ω)) : Set (Fin N → Ω) :=
  {z | cns ω z ∈ A}

lemma fh_le_of_mem {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (A : Set (Fin N → Ω))
    (x y : Fin N → Ω) (hy : y ∈ A) :
    fh h A x ≤ ∑ i, ENNReal.ofReal (if x i = y i then 0 else h (x i) (y i)) := by
  unfold fh
  exact iInf₂_le y hy

lemma le_fh {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (A : Set (Fin N → Ω)) (x : Fin N → Ω)
    (c : ℝ≥0∞)
    (hc : ∀ y ∈ A, c ≤ ∑ i, ENNReal.ofReal (if x i = y i then 0 else h (x i) (y i))) :
    c ≤ fh h A x := by
  unfold fh
  exact le_iInf₂ hc

lemma fh_cons_le {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y)
    (A : Set (Fin (N + 1) → Ω)) (ω ω' : Ω) (z : Fin N → Ω) :
    fh h A (cns ω z) ≤ ENNReal.ofReal (h ω ω') + fh h (sec ω' A) z := by
  show _ ≤ ENNReal.ofReal (h ω ω') + ⨅ y ∈ sec ω' A, _
  rw [ENNReal.add_iInf]
  refine le_iInf fun y => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hy => ?_
  calc fh h A (cns ω z)
      ≤ ∑ i, ENNReal.ofReal (if cns ω z i = cns ω' y i then 0
          else h (cns ω z i) (cns ω' y i)) := fh_le_of_mem h A _ _ hy
    _ ≤ _ := by
        rw [Fin.sum_univ_succ]
        simp only [cns_zero, cns_succ]
        apply add_le_add _ le_rfl
        split_ifs <;> simp [h_nonneg]

lemma fh_eq_zero_of_mem {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (A : Set (Fin N → Ω))
    (x : Fin N → Ω) (hx : x ∈ A) : fh h A x = 0 := by
  apply le_antisymm _ bot_le
  have := fh_le_of_mem h A x x hx
  simpa using this

/-! ### Product integrals without measurability -/

lemma lintegral_prod_le_iter {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (h : X × Y → ℝ≥0∞) :
    ∫⁻ p, h p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, h (x, y) ∂ν ∂μ := by
  rw [lintegral_def]
  refine iSup₂_le fun φ hφ => ?_
  calc φ.lintegral (μ.prod ν) = ∫⁻ p, φ p ∂(μ.prod ν) := (φ.lintegral_eq_lintegral _).symm
    _ = ∫⁻ x, ∫⁻ y, φ (x, y) ∂ν ∂μ := lintegral_prod _ φ.measurable.aemeasurable
    _ ≤ ∫⁻ x, ∫⁻ y, h (x, y) ∂ν ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hφ (x, y)

/-! ### The pointwise arithmetic inequality -/

/-- real version: `min(r, E) + min(1/r, E) ≤ E + 1/E` for `r > 0`, `E ≥ 1`. -/
lemma min_real (r E : ℝ) (hr : 0 < r) (hE : 1 ≤ E) :
    min r E + min r⁻¹ E ≤ E + E⁻¹ := by
  have hE0 : 0 < E := by linarith
  wlog h1 : 1 ≤ r generalizing r
  · have := this r⁻¹ (by positivity) (one_le_inv_iff₀.2 ⟨hr, by linarith⟩)
    rw [inv_inv] at this
    linarith
  have hri : r⁻¹ ≤ E := by
    calc r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
      _ ≤ E := hE
  rw [min_eq_left hri]
  rcases le_or_gt r E with h | h
  · rw [min_eq_left h]
    -- r + 1/r ≤ E + 1/E for 1 ≤ r ≤ E
    have : E + E⁻¹ - (r + r⁻¹) = (E - r) * (1 - (r * E)⁻¹) := by
      field_simp
      ring
    have h2 : 0 ≤ (E - r) * (1 - (r * E)⁻¹) := by
      apply mul_nonneg (by linarith)
      rw [sub_nonneg]
      apply inv_le_one_of_one_le₀
      nlinarith
    linarith
  · rw [min_eq_right h.le]
    have : r⁻¹ ≤ E⁻¹ := inv_anti₀ hE0 h.le
    linarith

lemma ofReal_min' (x y : ℝ) :
    ENNReal.ofReal (min x y) = min (ENNReal.ofReal x) (ENNReal.ofReal y) :=
  Monotone.map_min (fun _ _ h => ENNReal.ofReal_le_ofReal h)

/-- ENNReal version, positive reals. -/
lemma min_ennreal_pos (a b E : ℝ) (ha : 0 < a) (hb : 0 < b) (hE : 1 ≤ E) :
    min (ENNReal.ofReal a)⁻¹ (ENNReal.ofReal E / ENNReal.ofReal b) * ENNReal.ofReal b
      + min (ENNReal.ofReal b)⁻¹ (ENNReal.ofReal E / ENNReal.ofReal a) * ENNReal.ofReal a
      ≤ ENNReal.ofReal E + (ENNReal.ofReal E)⁻¹ := by
  have hE0 : 0 < E := by linarith
  rw [← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
    ← ENNReal.ofReal_inv_of_pos hE0, ← ENNReal.ofReal_div_of_pos hb,
    ← ENNReal.ofReal_div_of_pos ha,
    ← ofReal_min', ← ofReal_min',
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have key := min_real (b / a) E (by positivity) hE
  rw [inv_div] at key
  have h1 : min a⁻¹ (E / b) * b = min (b / a) E := by
    rcases le_total a⁻¹ (E / b) with h | h
    · rw [min_eq_left h, min_eq_left]
      · field_simp
      · rw [le_div_iff₀ hb, inv_mul_eq_div] at h; exact h
    · rw [min_eq_right h, min_eq_right]
      · field_simp
      · rw [div_le_iff₀ hb, inv_mul_eq_div] at h; exact h
  have h2 : min b⁻¹ (E / a) * a = min (a / b) E := by
    rcases le_total b⁻¹ (E / a) with h | h
    · rw [min_eq_left h, min_eq_left]
      · field_simp
      · rw [le_div_iff₀ ha, inv_mul_eq_div] at h; exact h
    · rw [min_eq_right h, min_eq_right]
      · field_simp
      · rw [div_le_iff₀ ha, inv_mul_eq_div] at h; exact h
  rw [h1, h2]
  exact key

/-- ENNReal version. -/
lemma min_ennreal (a b E : ℝ≥0∞) (ha : a ≤ 1) (hb : b ≤ 1) (hE1 : 1 ≤ E) (hEt : E ≠ ⊤) :
    min a⁻¹ (E / b) * b + min b⁻¹ (E / a) * a ≤ E + E⁻¹ := by
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hbt : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have hE0 : E ≠ 0 := by
    intro h; rw [h] at hE1; exact absurd hE1 (by simp)
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0
    rcases eq_or_ne b 0 with hb0 | hb0
    · subst hb0; simp
    · simp only [mul_zero, add_zero, ENNReal.inv_zero]
      rw [min_eq_right le_top, ENNReal.div_mul_cancel hb0 hbt]
      exact le_self_add
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    simp only [mul_zero, zero_add, ENNReal.inv_zero]
    rw [min_eq_right le_top, ENNReal.div_mul_cancel ha0 hat]
    exact le_self_add
  have ha' : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hb' : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  have hE' : 1 ≤ E.toReal := by
    have := ENNReal.toReal_mono hEt hE1
    simpa using this
  rw [← ENNReal.ofReal_toReal hat, ← ENNReal.ofReal_toReal hbt, ← ENNReal.ofReal_toReal hEt]
  exact min_ennreal_pos _ _ _ ha' hb' hE'

/-! ### The one-step inequality (ENNReal form of Proposition 2.4.2) -/

/-- The constant of Theorem 2.4.1. -/
noncomputable def Cst {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω → Ω → ℝ) (t : ℝ) :
    ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∫⁻ p : Ω × Ω,
    ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2))) ∂(μ.prod μ)

lemma two_le_exp_add_exp_neg (a : ℝ) : 2 ≤ Real.exp a + Real.exp (-a) := by
  have h1 := Real.add_one_le_exp a
  have h2 := Real.add_one_le_exp (-a)
  linarith

lemma one_le_Cst {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (t : ℝ) : 1 ≤ Cst μ h t := by
  unfold Cst
  have : (2 : ℝ≥0∞) ≤ ∫⁻ p : Ω × Ω,
      ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
        ∂(μ.prod μ) := by
    calc (2 : ℝ≥0∞) = ∫⁻ _ : Ω × Ω, (2 : ℝ≥0∞) ∂(μ.prod μ) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
          apply lintegral_mono
          intro p
          have := two_le_exp_add_exp_neg (t * vmax h p.1 p.2)
          calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
            _ ≤ _ := ENNReal.ofReal_le_ofReal this
  calc (1 : ℝ≥0∞) = (1 / 2) * 2 := by
        rw [one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl this

lemma Cst_ne_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (t : ℝ) : Cst μ h t ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_Cst μ h t))

lemma exp_vmax_eq (t : ℝ) (h : ℝ) :
    ENNReal.ofReal (Real.exp (t * h) + Real.exp (-(t * h)))
      = ENNReal.ofReal (Real.exp (t * h)) + (ENNReal.ofReal (Real.exp (t * h)))⁻¹ := by
  rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, Real.exp_neg,
    ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]

theorem one_step {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (t : ℝ) (ht : 0 ≤ t) (g : Ω → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ ω, g ω ≤ 1)
    (F : Ω → ℝ≥0∞)
    (hF : ∀ ω ω', F ω ≤ ENNReal.ofReal (Real.exp (t * h ω ω')) / g ω') :
    (∫⁻ ω, F ω ∂μ) * (∫⁻ ω, g ω ∂μ) ≤ Cst μ h t := by
  unfold Cst
  set I := ∫⁻ p : Ω × Ω,
    ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
      ∂(μ.prod μ) with hI
  clear_value I
  rw [lintegral_def, ENNReal.iSup_mul]
  simp_rw [ENNReal.iSup_mul]
  refine iSup₂_le fun φ hφ => ?_
  set Ψ : Ω × Ω → ℝ≥0∞ := fun p => φ p.1 * g p.2 with hΨ
  have hΨm : Measurable Ψ := (φ.measurable.comp measurable_fst).mul (hg.comp measurable_snd)
  have hswap : ∫⁻ p, Ψ p ∂(μ.prod μ) = ∫⁻ p, Ψ p.swap ∂(μ.prod μ) := by
    conv_lhs => rw [← Measure.prod_swap (μ := μ) (ν := μ)]
    rw [lintegral_map hΨm measurable_swap]
  have hpt : ∀ p : Ω × Ω, Ψ p + Ψ p.swap ≤
      ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2))) := by
    intro p
    set E := ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2)) with hE
    have hE1 : 1 ≤ E := by
      rw [hE, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.one_le_exp_iff]
      exact mul_nonneg ht (le_trans (h_nonneg _ _) (le_max_left _ _))
    have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
    have hF1 : ∀ ω, F ω ≤ (g ω)⁻¹ := by
      intro ω
      have := hF ω ω
      rwa [h_diag, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_div] at this
    have hF2 : F p.1 ≤ E / g p.2 := by
      calc F p.1 ≤ ENNReal.ofReal (Real.exp (t * h p.1 p.2)) / g p.2 := hF _ _
        _ ≤ E / g p.2 := by
            apply ENNReal.div_le_div_right
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.2
            exact mul_le_mul_of_nonneg_left (le_max_left _ _) ht
    have hF3 : F p.2 ≤ E / g p.1 := by
      calc F p.2 ≤ ENNReal.ofReal (Real.exp (t * h p.2 p.1)) / g p.1 := hF _ _
        _ ≤ E / g p.1 := by
            apply ENNReal.div_le_div_right
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.2
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) ht
    rw [exp_vmax_eq]
    calc Ψ p + Ψ p.swap = φ p.1 * g p.2 + φ p.2 * g p.1 := rfl
      _ ≤ min (g p.1)⁻¹ (E / g p.2) * g p.2 + min (g p.2)⁻¹ (E / g p.1) * g p.1 := by
          apply add_le_add
          · exact mul_le_mul' (le_min ((hφ p.1).trans (hF1 _)) ((hφ p.1).trans hF2)) le_rfl
          · exact mul_le_mul' (le_min ((hφ p.2).trans (hF1 _)) ((hφ p.2).trans hF3)) le_rfl
      _ ≤ E + E⁻¹ := min_ennreal _ _ _ (hg1 _) (hg1 _) hE1 hEt
  have h2 : 2 * ∫⁻ p, Ψ p ∂(μ.prod μ) ≤ I := by
    rw [two_mul]
    nth_rewrite 2 [hswap]
    rw [← lintegral_add_left hΨm, hI]
    exact lintegral_mono hpt
  calc φ.lintegral μ * ∫⁻ ω, g ω ∂μ = (∫⁻ ω, φ ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
        rw [φ.lintegral_eq_lintegral]
    _ = ∫⁻ p, Ψ p ∂(μ.prod μ) :=
        (lintegral_prod_mul φ.measurable.aemeasurable hg.aemeasurable).symm
    _ = 2⁻¹ * (2 * ∫⁻ p, Ψ p ∂(μ.prod μ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2⁻¹ * I := mul_le_mul' le_rfl h2
    _ = 1 / 2 * I := by rw [one_div]

/-! ### The main induction -/

theorem main_induction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ (N : ℕ) (A : Set (Fin N → Ω)), MeasurableSet A →
      (∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin N => μ))
        ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ * Cst μ h t ^ N := by
  intro N
  induction N with
  | zero =>
    intro A _
    rcases Set.eq_empty_or_nonempty A with hA | ⟨y, hy⟩
    · subst hA
      rw [measure_empty, ENNReal.inv_zero, pow_zero, mul_one]
      exact le_top
    · have hall : ∀ x, x ∈ A := fun x => by rwa [Subsingleton.elim x y]
      have hS : (∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin 0 => μ)) = 1 := by
        simp_rw [fun x => fh_eq_zero_of_mem h A x (hall x), ex_zero']
        rw [lintegral_const, measure_univ, mul_one]
      rw [hS, pow_zero, mul_one, ENNReal.one_le_inv]
      exact prob_le_one
  | succ N ih =>
    intro A hA
    set ν : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => μ with hν
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Ω) 0 with he
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (N + 1) => μ) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => μ) 0
    have hsymm : ∀ p : Ω × (Fin N → Ω), e.symm p = cns p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      show Fin.insertNth (α := fun _ => Ω) 0 p.1 p.2 = _
      rw [Fin.insertNth_zero']
      rfl
    set S := e.symm ⁻¹' A with hS
    have hSm : MeasurableSet S := e.symm.measurable hA
    set g : Ω → ℝ≥0∞ := fun ω => ν (Prod.mk ω ⁻¹' S) with hg
    have hgm : Measurable g := measurable_measure_prodMk_left hSm
    have hg1 : ∀ ω, g ω ≤ 1 := fun ω => prob_le_one
    have hsec : ∀ ω, Prod.mk ω ⁻¹' S = sec ω A := by
      intro ω
      ext z
      simp [hS, sec, hsymm]
    have hgsec : ∀ ω, g ω = ν (sec ω A) := by
      intro ω
      simp only [hg]
      rw [hsec]
    have hsecm : ∀ ω, MeasurableSet (sec ω A) := by
      intro ω
      rw [← hsec]
      exact measurable_prodMk_left hSm
    have hPA : (Measure.pi fun _ : Fin (N + 1) => μ) A = ∫⁻ ω, g ω ∂μ := by
      rw [← mp.symm.measure_preimage_equiv A, Measure.prod_apply hSm]
    have hL : (∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin (N + 1) => μ))
        = ∫⁻ p, ex t (fh h A (cns p.1 p.2)) ∂(μ.prod ν) := by
      rw [MeasurePreserving.lintegral_map_equiv _ e.symm mp.symm]
      simp_rw [hsymm]
    set C := Cst μ h t with hC
    have hC0 : C ≠ 0 := Cst_ne_zero μ h t
    have hAt : ((Measure.pi fun _ : Fin (N + 1) => μ) A)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
    rcases eq_or_ne C ⊤ with hCt | hCt
    · rw [hCt, ENNReal.top_pow (Nat.succ_ne_zero N), ENNReal.mul_top hAt]
      exact le_top
    have hCN : C ^ N ≠ ⊤ := ENNReal.pow_ne_top hCt
    have hCN0 : C ^ N ≠ 0 := pow_ne_zero _ hC0
    set F : Ω → ℝ≥0∞ := fun ω => ⨅ ω', ENNReal.ofReal (Real.exp (t * h ω ω')) / g ω' with hF
    have hFle : ∀ ω ω', F ω ≤ ENNReal.ofReal (Real.exp (t * h ω ω')) / g ω' :=
      fun ω ω' => iInf_le _ ω'
    have hinner : ∀ ω, (∫⁻ z, ex t (fh h A (cns ω z)) ∂ν) ≤ F ω * C ^ N := by
      intro ω
      rw [hF]
      show _ ≤ (⨅ ω', ENNReal.ofReal (Real.exp (t * h ω ω')) / g ω') * C ^ N
      rw [ENNReal.iInf_mul_of_ne hCN0 hCN]
      refine le_iInf fun ω' => ?_
      calc (∫⁻ z, ex t (fh h A (cns ω z)) ∂ν)
          ≤ ∫⁻ z, ex t (ENNReal.ofReal (h ω ω') + fh h (sec ω' A) z) ∂ν :=
            lintegral_mono fun z => ex_mono t ht (fh_cons_le h h_nonneg A ω ω' z)
        _ = ∫⁻ z, ENNReal.ofReal (Real.exp (t * h ω ω')) * ex t (fh h (sec ω' A) z) ∂ν := by
            simp_rw [ex_add_const t ht _ (h_nonneg ω ω')]
        _ = ENNReal.ofReal (Real.exp (t * h ω ω')) * ∫⁻ z, ex t (fh h (sec ω' A) z) ∂ν :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Real.exp (t * h ω ω')) * ((ν (sec ω' A))⁻¹ * C ^ N) :=
            mul_le_mul' le_rfl (ih _ (hsecm ω'))
        _ = ENNReal.ofReal (Real.exp (t * h ω ω')) / g ω' * C ^ N := by
            rw [hgsec, div_eq_mul_inv, mul_assoc]
    have hstep := one_step μ h h_nonneg h_diag t ht g hgm hg1 F hFle
    rw [← hC] at hstep
    calc (∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin (N + 1) => μ))
        = ∫⁻ p, ex t (fh h A (cns p.1 p.2)) ∂(μ.prod ν) := hL
      _ ≤ ∫⁻ ω, ∫⁻ z, ex t (fh h A (cns ω z)) ∂ν ∂μ := lintegral_prod_le_iter μ ν _
      _ ≤ ∫⁻ ω, F ω * C ^ N ∂μ := lintegral_mono hinner
      _ = (∫⁻ ω, F ω ∂μ) * C ^ N := lintegral_mul_const' _ _ hCN
      _ ≤ ((Measure.pi fun _ : Fin (N + 1) => μ) A)⁻¹ * C ^ (N + 1) := by
          rw [hPA, pow_succ]
          set u := ∫⁻ ω, g ω ∂μ with hu
          rcases eq_or_ne u 0 with h0 | h0
          · rw [h0, ENNReal.inv_zero, ENNReal.top_mul (mul_ne_zero hCN0 hC0)]
            exact le_top
          have hu1 : u ≤ 1 := by
            rw [hu]
            calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hg1
              _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
          have hut : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
          have hFu : (∫⁻ ω, F ω ∂μ) ≤ u⁻¹ * C := by
            rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hut)]
            exact hstep
          calc (∫⁻ ω, F ω ∂μ) * C ^ N ≤ (u⁻¹ * C) * C ^ N := mul_le_mul' hFu le_rfl
            _ = u⁻¹ * (C ^ N * C) := by ring

theorem theorem_2_4_1_core
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (_h_meas : Measurable (Function.uncurry h))
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (_hfA : Measurable (fh h A))
    (t : ℝ) (ht : 0 < t)
    (_h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (t * h p.1 p.2)) ∂(μ.prod μ) ≠ ⊤) :
    ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ((1 / 2 : ENNReal) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ)) ^ N :=
  main_induction μ h h_nonneg h_diag t ht.le N A hA


lemma cosh_mul_le (t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cosh (t * v) ≤ t ^ 2 * Real.cosh v + (1 - t ^ 2) := by
  have hA := Real.hasSum_cosh (t * v)
  have hB := ((Real.hasSum_cosh v).mul_left (t ^ 2)).add (hasSum_ite_eq (0 : ℕ) (1 - t ^ 2))
  refine hasSum_le (fun n => ?_) hA hB
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · simp only [if_neg hn.ne', add_zero]
    rw [mul_pow, mul_div_assoc]
    have : t ^ (2 * n) ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by omega)
    exact mul_le_mul_of_nonneg_right this (div_nonneg (Even.pow_nonneg ⟨n, by ring⟩ v) (by positivity))

lemma exp_add_exp_neg_mul_le (t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t * v) + Real.exp (-(t * v)) ≤ 2 + t ^ 2 * (Real.exp v + Real.exp (-v) - 2) := by
  have h := cosh_mul_le t v ht0 ht1
  rw [Real.cosh_eq, Real.cosh_eq] at h
  linarith

lemma ofReal_exp_pow (x : ℝ) (n : ℕ) :
    ENNReal.ofReal (Real.exp x) ^ n = ENNReal.ofReal (Real.exp ((n : ℝ) * x)) := by
  rw [Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le]


theorem theorem_2_4_3_core
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (_hfA : Measurable (fh h A))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp ((N : ℝ) * t ^ 2 *
          (∫⁻ p : Ω × Ω, ENNReal.ofReal
              (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2) ∂(μ.prod μ)).toReal)) := by
  set J := ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2)
    ∂(μ.prod μ) with hJ
  have hJt : J ≠ ⊤ := by
    refine ne_top_of_le_ne_top h_int (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (-h p.1 p.2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [h_nonneg p.1 p.2]
    linarith
  set f : Ω × Ω → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2) with hf
  have hh : Measurable fun p : Ω × Ω => h p.1 p.2 := h_meas
  have hfm : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    exact ((Real.measurable_exp.comp hh).add (Real.measurable_exp.comp hh.neg)).sub
      measurable_const
  have hswap : ∫⁻ p, f p.swap ∂(μ.prod μ) = J := by
    rw [hJ]
    conv_rhs => rw [← Measure.prod_swap (μ := μ) (ν := μ)]
    rw [lintegral_map hfm measurable_swap]
  have hJv : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (vmax h p.1 p.2)
      + Real.exp (-vmax h p.1 p.2) - 2) ∂(μ.prod μ) ≤ 2 * J := by
    calc _ ≤ ∫⁻ p, (f p + f p.swap) ∂(μ.prod μ) := by
          apply lintegral_mono
          intro p
          show ENNReal.ofReal (Real.exp (vmax h p.1 p.2) + Real.exp (-vmax h p.1 p.2) - 2)
            ≤ ENNReal.ofReal (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2)
              + ENNReal.ofReal (Real.exp (h p.2 p.1) + Real.exp (-h p.2 p.1) - 2)
          unfold vmax
          rcases le_total (h p.1 p.2) (h p.2 p.1) with hle | hle
          · rw [max_eq_right hle]; exact le_add_self
          · rw [max_eq_left hle]; exact le_self_add
      _ = J + J := by rw [lintegral_add_left hfm, hswap]
      _ = 2 * J := (two_mul J).symm
  have hC : Cst μ h t ≤ ENNReal.ofReal (Real.exp (t ^ 2 * J.toReal)) := by
    unfold Cst
    have h12 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
      rw [one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
    calc (1 / 2 : ℝ≥0∞) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ)
        ≤ (1 / 2 : ℝ≥0∞) * ∫⁻ p : Ω × Ω, (2 + ENNReal.ofReal (t ^ 2) *
            ENNReal.ofReal (Real.exp (vmax h p.1 p.2) + Real.exp (-vmax h p.1 p.2) - 2))
            ∂(μ.prod μ) := by
          apply mul_le_mul' le_rfl
          apply lintegral_mono
          intro p
          have h2 := two_le_exp_add_exp_neg (vmax h p.1 p.2)
          calc ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
              ≤ ENNReal.ofReal (2 + t ^ 2 *
                  (Real.exp (vmax h p.1 p.2) + Real.exp (-vmax h p.1 p.2) - 2)) :=
                ENNReal.ofReal_le_ofReal (exp_add_exp_neg_mul_le t _ ht0 ht1)
            _ = _ := by
                rw [ENNReal.ofReal_add (by norm_num) (by nlinarith),
                  ENNReal.ofReal_mul (by positivity)]
                norm_num
      _ = (1 / 2 : ℝ≥0∞) * (2 + ENNReal.ofReal (t ^ 2) * ∫⁻ p : Ω × Ω,
            ENNReal.ofReal (Real.exp (vmax h p.1 p.2) + Real.exp (-vmax h p.1 p.2) - 2)
            ∂(μ.prod μ)) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (1 / 2 : ℝ≥0∞) * (2 + ENNReal.ofReal (t ^ 2) * (2 * J)) := by
          gcongr
      _ = (1 / 2 : ℝ≥0∞) * 2 + ((1 / 2 : ℝ≥0∞) * 2) * (ENNReal.ofReal (t ^ 2) * J) := by
          ring
      _ = 1 + ENNReal.ofReal (t ^ 2) * J := by rw [h12, one_mul]
      _ = ENNReal.ofReal (1 + t ^ 2 * J.toReal) := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hJt]
      _ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * J.toReal)) :=
          ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (t ^ 2 * J.toReal)])
  calc ∫⁻ x, EReal.exp ((t : EReal) * (fh h A x : EReal)) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ * Cst μ h t ^ N :=
        main_induction μ h h_nonneg h_diag t ht0 N A hA
    _ ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ * ENNReal.ofReal (Real.exp (t ^ 2 * J.toReal)) ^ N :=
        mul_le_mul' le_rfl (pow_le_pow_left' hC N)
    _ = _ := by simp only [ofReal_exp_pow, mul_assoc]

/-- Markov-type bound for the level sets of `fh`. -/
lemma measure_level_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (N : ℕ) (A : Set (Fin N → Ω)) (hfA : Measurable (fh h A))
    (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu : 0 ≤ u) (R : ℝ≥0∞)
    (hR : ∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin N => μ) ≤ R) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ ENNReal.ofReal (Real.exp (-(t * u))) * R := by
  set P := Measure.pi fun _ : Fin N => μ
  set S := {x | ENNReal.ofReal u ≤ fh h A x} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hfA
  set E := ENNReal.ofReal (Real.exp (t * u)) with hE
  have hE0 : E ≠ 0 := by
    rw [hE]; exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : E * P S ≤ R := by
    rw [← lintegral_indicator_const hSm]
    refine le_trans (lintegral_mono fun x => ?_) hR
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hE, ← ex_ofReal t ht u hu]
      exact ex_mono t ht hx
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  calc P S = E⁻¹ * (E * P S) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hE0 hEt, one_mul]
    _ ≤ E⁻¹ * R := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (Real.exp (-(t * u))) * R := by
        rw [hE, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]

theorem corollary_2_4_4_core
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_int : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ) ≤ 2)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 2 * N) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp (-(u ^ 2) / (4 * N))) := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hu' : u = 0 := by
      have : u ≤ 0 := by simpa using hu
      linarith
    subst hu'
    have : {x : Fin 0 → Ω | ENNReal.ofReal 0 ≤ fh h A x} = Set.univ := by
      ext x; simp
    rw [this, measure_univ]
    simp only [zero_pow (two_ne_zero), neg_zero, CharP.cast_eq_zero, mul_zero, div_zero,
      Real.exp_zero, ENNReal.ofReal_one, mul_one]
    exact ENNReal.one_le_inv.2 prob_le_one
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t := u / (2 * N) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; exact hu
  have hint : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofNat_ne_top h_int
  set J := ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2) + Real.exp (-h p.1 p.2) - 2)
    ∂(μ.prod μ) with hJ
  have hh : Measurable fun p : Ω × Ω => h p.1 p.2 := h_meas
  have hJ1 : J ≤ 1 := by
    have hle : J ≤ ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2) - 1) ∂(μ.prod μ) := by
      apply lintegral_mono
      intro p
      apply ENNReal.ofReal_le_ofReal
      have : Real.exp (-h p.1 p.2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith [h_nonneg p.1 p.2]
      linarith
    have heq : ∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2)) ∂(μ.prod μ)
        = (∫⁻ p : Ω × Ω, ENNReal.ofReal (Real.exp (h p.1 p.2) - 1) ∂(μ.prod μ)) + 1 := by
      have : (1 : ℝ≥0∞) = ∫⁻ _ : Ω × Ω, (1 : ℝ≥0∞) ∂(μ.prod μ) := by
        rw [lintegral_const, measure_univ, mul_one]
      rw [this, ← lintegral_add_right _ measurable_const]
      congr 1
      ext p
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add _ zero_le_one, sub_add_cancel]
      linarith [Real.add_one_le_exp (h p.1 p.2), h_nonneg p.1 p.2]
    rw [heq, ← one_add_one_eq_two] at h_int
    exact hle.trans (ENNReal.le_of_add_le_add_right ENNReal.one_ne_top h_int)
  have hJr : J.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hJ1
    simpa using this
  have hJr0 : 0 ≤ J.toReal := ENNReal.toReal_nonneg
  have h243 := theorem_2_4_3_core μ h h_nonneg h_diag h_meas hint N A hA hfA t ht0 ht1
  rw [← hJ] at h243
  have hM := measure_level_le μ h N A hfA t ht0 u hu0 _ h243
  refine hM.trans ?_
  rw [← mul_assoc, mul_comm (ENNReal.ofReal _) _, mul_assoc]
  apply mul_le_mul' le_rfl
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have h1 : (N : ℝ) * t ^ 2 * J.toReal ≤ (N : ℝ) * t ^ 2 :=
    mul_le_of_le_one_right (by positivity) hJr
  have h2 : -(t * u) + (N : ℝ) * t ^ 2 = -(u ^ 2) / (4 * N) := by
    rw [ht]; field_simp; ring
  linarith

/-! ### Corollary 2.4.5 -/

lemma cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  linarith

lemma exp_add_exp_neg_le_sq (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x + Real.exp (-x) ≤ 2 + 2 * x ^ 2 := by
  have h := cosh_mul_le x 1 hx0 hx1
  rw [mul_one, Real.cosh_eq] at h
  have h2 := cosh_one_le_two
  nlinarith

/-- Exponential moment bound in the Bernstein regime `t h ≤ 1`. -/
theorem moment_bernstein
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (hQ : ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (t : ℝ) (ht0 : 0 ≤ t) (hth : ∀ x y, t * h x y ≤ 1) :
    ∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        ENNReal.ofReal (Real.exp ((N : ℝ) * (2 * t ^ 2 *
          (∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ)).toReal))) := by
  set Q := ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ) with hQdef
  set f : Ω × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (h p.1 p.2 ^ 2) with hf
  have hh : Measurable fun p : Ω × Ω => h p.1 p.2 := h_meas
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (hh.pow_const 2)
  have hswap : ∫⁻ p, f p.swap ∂(μ.prod μ) = Q := by
    rw [hQdef]
    conv_rhs => rw [← Measure.prod_swap (μ := μ) (ν := μ)]
    rw [lintegral_map hfm measurable_swap]
  have hQv : ∫⁻ p : Ω × Ω, ENNReal.ofReal (vmax h p.1 p.2 ^ 2) ∂(μ.prod μ) ≤ 2 * Q := by
    calc _ ≤ ∫⁻ p, (f p + f p.swap) ∂(μ.prod μ) := by
          apply lintegral_mono
          intro p
          show ENNReal.ofReal (vmax h p.1 p.2 ^ 2)
            ≤ ENNReal.ofReal (h p.1 p.2 ^ 2) + ENNReal.ofReal (h p.2 p.1 ^ 2)
          unfold vmax
          rcases le_total (h p.1 p.2) (h p.2 p.1) with hle | hle
          · rw [max_eq_right hle]; exact le_add_self
          · rw [max_eq_left hle]; exact le_self_add
      _ = Q + Q := by rw [lintegral_add_left hfm, hswap]
      _ = 2 * Q := (two_mul Q).symm
  have hC : Cst μ h t ≤ ENNReal.ofReal (Real.exp (2 * t ^ 2 * Q.toReal)) := by
    unfold Cst
    have h12 : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
      rw [one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
    calc (1 / 2 : ℝ≥0∞) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ)
        ≤ (1 / 2 : ℝ≥0∞) * ∫⁻ p : Ω × Ω, (2 + ENNReal.ofReal (2 * t ^ 2) *
            ENNReal.ofReal (vmax h p.1 p.2 ^ 2)) ∂(μ.prod μ) := by
          apply mul_le_mul' le_rfl
          apply lintegral_mono
          intro p
          have hv0 : 0 ≤ t * vmax h p.1 p.2 :=
            mul_nonneg ht0 (le_trans (h_nonneg _ _) (le_max_left _ _))
          have hv1 : t * vmax h p.1 p.2 ≤ 1 := by
            unfold vmax
            rcases le_total (h p.1 p.2) (h p.2 p.1) with hle | hle
            · rw [max_eq_right hle]; exact hth _ _
            · rw [max_eq_left hle]; exact hth _ _
          calc ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
              ≤ ENNReal.ofReal (2 + 2 * t ^ 2 * vmax h p.1 p.2 ^ 2) := by
                apply ENNReal.ofReal_le_ofReal
                have := exp_add_exp_neg_le_sq _ hv0 hv1
                rw [mul_pow] at this
                linarith
            _ = _ := by
                rw [ENNReal.ofReal_add (by norm_num) (by positivity),
                  ENNReal.ofReal_mul (by positivity)]
                norm_num
      _ = (1 / 2 : ℝ≥0∞) * (2 + ENNReal.ofReal (2 * t ^ 2) * ∫⁻ p : Ω × Ω,
            ENNReal.ofReal (vmax h p.1 p.2 ^ 2) ∂(μ.prod μ)) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (1 / 2 : ℝ≥0∞) * (2 + ENNReal.ofReal (2 * t ^ 2) * (2 * Q)) := by
          gcongr
      _ = (1 / 2 : ℝ≥0∞) * 2 + ((1 / 2 : ℝ≥0∞) * 2) * (ENNReal.ofReal (2 * t ^ 2) * Q) := by
          ring
      _ = 1 + ENNReal.ofReal (2 * t ^ 2) * Q := by rw [h12, one_mul]
      _ = ENNReal.ofReal (1 + 2 * t ^ 2 * Q.toReal) := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (q := Q.toReal) (by positivity), ENNReal.ofReal_toReal hQ]
      _ ≤ ENNReal.ofReal (Real.exp (2 * t ^ 2 * Q.toReal)) :=
          ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (2 * t ^ 2 * Q.toReal)])
  calc ∫⁻ x, ex t (fh h A x) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ * Cst μ h t ^ N :=
        main_induction μ h h_nonneg h_diag t ht0 N A hA
    _ ≤ ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
          ENNReal.ofReal (Real.exp (2 * t ^ 2 * Q.toReal)) ^ N :=
        mul_le_mul' le_rfl (pow_le_pow_left' hC N)
    _ = _ := by rw [ofReal_exp_pow]

lemma ereal_exp_neg_coe (m : ℝ≥0∞) (hm : m ≠ ⊤) :
    EReal.exp (-(m : EReal)) = ENNReal.ofReal (Real.exp (-m.toReal)) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hm]
  rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg, ← EReal.coe_neg,
    EReal.exp_coe]

theorem corollary_2_4_5_core
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_sup_fin : (⨆ x, ⨆ y, ENNReal.ofReal (h x y)) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ if (Measure.pi fun _ : Fin N => μ) A = 0 then ⊤ else
        ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        EReal.exp (-((min
          (ENNReal.ofReal (u ^ 2) /
            (8 * (N : ENNReal) * ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ)))
          (ENNReal.ofReal u / (2 * ⨆ x, ⨆ y, ENNReal.ofReal (h x y))) : ENNReal) : EReal)) := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  set H := ⨆ x, ⨆ y, ENNReal.ofReal (h x y) with hH
  set Q := ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ) with hQ
  set S := {x | ENNReal.ofReal u ≤ fh h A x} with hS
  split_ifs with hA0
  · exact le_top
  set a := ENNReal.ofReal (u ^ 2) / (8 * (N : ℝ≥0∞) * Q) with ha
  set b := ENNReal.ofReal u / (2 * H) with hb
  have hPA1 : 1 ≤ (P A)⁻¹ := ENNReal.one_le_inv.2 prob_le_one
  have hS1 : P S ≤ 1 := prob_le_one
  -- the case u ≤ 0
  rcases le_or_gt u 0 with hu | hu
  · have hb0 : b = 0 := by rw [hb, ENNReal.ofReal_eq_zero.2 hu, ENNReal.zero_div]
    have : min a b = 0 := by rw [hb0]; exact min_eq_right bot_le
    rw [this, EReal.coe_ennreal_zero, neg_zero, EReal.exp_zero, mul_one]
    exact hS1.trans hPA1
  -- u > 0
  have hHt : H ≠ ⊤ := h_sup_fin
  have hhH : ∀ x y, ENNReal.ofReal (h x y) ≤ H :=
    fun x y => le_iSup₂ (f := fun x y => ENNReal.ofReal (h x y)) x y
  set Hr := H.toReal with hHr_def
  have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
  have hhHr : ∀ x y, h x y ≤ Hr := by
    intro x y
    have := ENNReal.toReal_mono hHt (hhH x y)
    rwa [ENNReal.toReal_ofReal (h_nonneg x y)] at this
  rcases eq_or_lt_of_le hHr0 with hHr | hHr
  · -- h ≡ 0
    have hh0 : ∀ x y, h x y = 0 :=
      fun x y => le_antisymm (by rw [hHr]; exact hhHr x y) (h_nonneg x y)
    have hAne : A.Nonempty := by
      rcases Set.eq_empty_or_nonempty A with hAe | hAe
      · exact absurd (by rw [hAe, measure_empty]) hA0
      · exact hAe
    have hfh0 : ∀ x, fh h A x = 0 := by
      intro x
      obtain ⟨y, hy⟩ := hAne
      apply le_antisymm _ bot_le
      refine (fh_le_of_mem h A x y hy).trans ?_
      simp [hh0]
    have hSe : S = ∅ := by
      ext x
      simp only [hS, Set.mem_setOf_eq, hfh0, Set.mem_empty_iff_false, iff_false, not_le]
      exact ENNReal.ofReal_pos.2 hu
    rw [hSe, measure_empty]
    exact bot_le
  -- Hr > 0
  have hH0 : H ≠ 0 := by
    intro h0
    have : Hr = 0 := by rw [hHr_def, h0, ENNReal.toReal_zero]
    linarith
  have hbt : b ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top (mul_ne_zero two_ne_zero hH0)
  have hbr : b.toReal = u / (2 * Hr) := by
    rw [hb, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le, ← hHr_def]
    norm_num
  have hmt : min a b ≠ ⊤ := ne_top_of_le_ne_top hbt (min_le_right _ _)
  rw [ereal_exp_neg_coe _ hmt]
  set m := (min a b).toReal with hm
  have hmb : m ≤ u / (2 * Hr) := by
    rw [hm, ← hbr]; exact ENNReal.toReal_mono hbt (min_le_right _ _)
  -- The case Q = ⊤ with N ≥ 1
  by_cases hQN : Q = ⊤ ∧ N ≠ 0
  · have ha0 : a = 0 := by
      rw [ha, hQN.1, ENNReal.mul_top (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.2 hQN.2)),
        ENNReal.div_top]
    have hm0 : m = 0 := by rw [hm, ha0, min_eq_left (zero_le' (a := b)), ENNReal.toReal_zero]
    rw [hm0, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
    exact hS1.trans hPA1
  -- general moment bound
  set q := Q.toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hmom : ∀ t, 0 ≤ t → t * Hr ≤ 1 → ∫⁻ x, ex t (fh h A x) ∂P
      ≤ (P A)⁻¹ * ENNReal.ofReal (Real.exp ((N : ℝ) * (2 * t ^ 2 * q))) := by
    intro t ht0 htH
    have hth : ∀ x y, t * h x y ≤ 1 :=
      fun x y => (mul_le_mul_of_nonneg_left (hhHr x y) ht0).trans htH
    rcases eq_or_ne N 0 with hN | hN
    · subst hN
      simp only [Nat.cast_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
      have := main_induction μ h h_nonneg h_diag t ht0 0 A hA
      rwa [pow_zero] at this
    · have hQt : Q ≠ ⊤ := fun hQt => hQN ⟨hQt, hN⟩
      exact moment_bernstein μ h h_nonneg h_diag h_meas hQt N A hA t ht0 hth
  have hmark : ∀ t, 0 ≤ t → t * Hr ≤ 1 → P S
      ≤ (P A)⁻¹ * ENNReal.ofReal (Real.exp (-(t * u) + (N : ℝ) * (2 * t ^ 2 * q))) := by
    intro t ht0 htH
    have := measure_level_le μ h N A hfA t ht0 u hu.le _ (hmom t ht0 htH)
    refine this.trans (le_of_eq ?_)
    rw [← mul_assoc, mul_comm (ENNReal.ofReal _) _, mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  suffices key : ∃ t, 0 ≤ t ∧ t * Hr ≤ 1 ∧ -(t * u) + (N : ℝ) * (2 * t ^ 2 * q) ≤ -m by
    obtain ⟨t, ht0, htH, hle⟩ := key
    exact (hmark t ht0 htH).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hle)))
  set n := (N : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg N
  have hHinv : 1 / Hr * Hr ≤ 1 := by rw [one_div, inv_mul_cancel₀ hHr.ne']
  have hub : u / (2 * Hr) ≤ 1 / Hr * u := by
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases hnq : n * q = 0
  · refine ⟨1 / Hr, by positivity, hHinv, ?_⟩
    have : n * (2 * (1 / Hr) ^ 2 * q) = 0 := by
      rw [show n * (2 * (1 / Hr) ^ 2 * q) = (n * q) * (2 * (1 / Hr) ^ 2) by ring, hnq, zero_mul]
    rw [this, add_zero, neg_le_neg_iff]
    exact hmb.trans hub
  · have hnq' : 0 < n * q := lt_of_le_of_ne (by positivity) (Ne.symm hnq)
    have hN : N ≠ 0 := by
      rintro rfl
      simp [hn] at hnq
    have hQt : Q ≠ ⊤ := fun hQt => hQN ⟨hQt, hN⟩
    have hq' : 0 < q := by
      rcases eq_or_lt_of_le hq0 with hq1 | hq1
      · rw [← hq1, mul_zero] at hnq'; exact absurd hnq' (lt_irrefl 0)
      · exact hq1
    have hQ0 : Q ≠ 0 := by
      intro h0
      have : q = 0 := by rw [hq, h0, ENNReal.toReal_zero]
      linarith
    have hat : a ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.2 hN)) hQ0)
    have har : a.toReal = u ^ 2 / (8 * n * q) := by
      rw [ha, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, ← hq, ← hn]
      norm_num
    have hma : m ≤ u ^ 2 / (8 * n * q) := by
      rw [hm, ← har]; exact ENNReal.toReal_mono hat (min_le_left _ _)
    set t₁ := u / (4 * n * q) with ht₁
    have ht₁0 : 0 ≤ t₁ := by positivity
    rcases le_or_gt (t₁ * Hr) 1 with hcase | hcase
    · refine ⟨t₁, ht₁0, hcase, ?_⟩
      have : -(t₁ * u) + n * (2 * t₁ ^ 2 * q) = -(u ^ 2 / (8 * n * q)) := by
        rw [ht₁]; field_simp; ring
      rw [this, neg_le_neg_iff]; exact hma
    · refine ⟨1 / Hr, by positivity, hHinv, ?_⟩
      have h4 : 4 * n * q < u * Hr := by
        rw [ht₁, div_mul_eq_mul_div, one_lt_div (by positivity)] at hcase; exact hcase
      have : -(1 / Hr * u) + n * (2 * (1 / Hr) ^ 2 * q) ≤ -(u / (2 * Hr)) := by
        rw [show -(1 / Hr * u) + n * (2 * (1 / Hr) ^ 2 * q)
            = (4 * n * q - 2 * u * Hr) / (2 * Hr ^ 2) by field_simp; ring,
          show -(u / (2 * Hr)) = (-(u * Hr)) / (2 * Hr ^ 2) by field_simp]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      exact this.trans (neg_le_neg hmb)

end TalagrandConc.Penalties

open TalagrandConc.Penalties


theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_sup_fin : (⨆ x, ⨆ y, ENNReal.ofReal (h x y)) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ if (Measure.pi fun _ : Fin N => μ) A = 0 then ⊤ else
        ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        EReal.exp (-((min
          (ENNReal.ofReal (u ^ 2) /
            (8 * (N : ENNReal) * ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ)))
          (ENNReal.ofReal u / (2 * ⨆ x, ⨆ y, ENNReal.ofReal (h x y))) : ENNReal) : EReal)) := by
  exact corollary_2_4_5_core μ h h_nonneg h_diag h_meas h_sup_fin N A hA hfA u
