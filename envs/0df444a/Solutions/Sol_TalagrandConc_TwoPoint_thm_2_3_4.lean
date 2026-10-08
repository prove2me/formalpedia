-- Prove2me | solution 1 for TalagrandConc.TwoPoint.thm_2_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:05:15.607053+00:00
-- url     : https://prove2.me/submissions/8a9d245a-6fae-42c0-bc42-c83dfb124d1b

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal


namespace TalagrandConc.TwoPoint

/-- The real-valued key inequality behind case 2 of Lemma 2.3.5: for
`e^{-t/α} ≤ u ≤ 1`, `(1 - p + p u^{-α}) (p₁ u + 1 - p₁)^α ≤ a(α,t)`. -/
lemma keyF (p p₁ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ p₁) (hq1 : p₁ ≤ 1)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hue : Real.exp (-t / α) ≤ u) :
    (1 - p + p * u ^ (-α)) * (p₁ * u + 1 - p₁) ^ α ≤ aConst α t p p₁ := by
  unfold aConst
  set c₂ : ℝ := p₁ * Real.exp (-t / α) + 1 - p₁ with hc₂
  set c₁ : ℝ := 1 - p + p * Real.exp t with hc₁
  have hc₂0 : 0 ≤ c₂ := by
    have := Real.exp_pos (-t / α)
    nlinarith
  have hc₁0 : 0 ≤ c₁ := by
    have := Real.exp_pos t
    nlinarith
  have hc0 : 0 ≤ c₁ * c₂ ^ α := mul_nonneg hc₁0 (Real.rpow_nonneg hc₂0 _)
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- t = 0 forces u = 1
    subst ht0
    have : u = 1 := by
      have h := hue
      simp at h
      linarith
    subst this
    simp
  · -- t > 0: interpolate between u₀ = e^{-t/α} and 1
    set e₀ : ℝ := Real.exp (-t / α) with he₀
    have he₀pos : 0 < e₀ := Real.exp_pos _
    have hlog_e₀ : Real.log e₀ = -t / α := by rw [he₀, Real.log_exp]
    have hlog_e₀neg : Real.log e₀ < 0 := by
      rw [hlog_e₀]; exact div_neg_of_neg_of_pos (by linarith) hα
    have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
    have hlogu' : Real.log e₀ ≤ Real.log u := Real.log_le_log he₀pos hue
    set θ : ℝ := Real.log u / Real.log e₀ with hθ
    have hθ0 : 0 ≤ θ := div_nonneg_of_nonpos hlogu hlog_e₀neg.le
    have hθ1 : θ ≤ 1 := by
      rw [hθ, div_le_one_of_neg hlog_e₀neg]; exact hlogu'
    have hu_eq : e₀ ^ θ = u := by
      rw [Real.rpow_def_of_pos he₀pos, hθ, mul_div_cancel₀ _ hlog_e₀neg.ne, Real.exp_log hu0]
    have he₀α : e₀ ^ (-α) = Real.exp t := by
      rw [he₀, ← Real.exp_mul]; congr 1; field_simp
    -- concavity of x ↦ x^θ on [0, ∞)
    have hconc := Real.concaveOn_rpow hθ0 hθ1
    -- (ii)
    have hii : 1 - p + p * u ^ (-α) ≤ c₁ ^ θ := by
      have h := hconc.2 (show (1:ℝ) ∈ Set.Ici 0 by simp)
        (show Real.exp t ∈ Set.Ici 0 by simp; positivity)
        (show 0 ≤ 1 - p by linarith) hp0 (show (1 - p) + p = 1 by ring)
      simp only [smul_eq_mul, Real.one_rpow, mul_one] at h
      have hu' : u ^ (-α) = (Real.exp t) ^ θ := by
        rw [← hu_eq, ← Real.rpow_mul he₀pos.le, mul_comm, Real.rpow_mul he₀pos.le, he₀α]
      rw [hu', hc₁]
      exact h
    -- (i)
    have hi : p₁ * u + 1 - p₁ ≤ c₂ ^ θ := by
      have h := hconc.2 (show e₀ ∈ Set.Ici 0 by simp; positivity)
        (show (1:ℝ) ∈ Set.Ici 0 by simp) hq0 (show 0 ≤ 1 - p₁ by linarith)
        (show p₁ + (1 - p₁) = 1 by ring)
      simp only [smul_eq_mul, Real.one_rpow, mul_one] at h
      rw [← hu_eq, hc₂]
      calc p₁ * e₀ ^ θ + 1 - p₁ = p₁ * e₀ ^ θ + (1 - p₁) := by ring
        _ ≤ (p₁ * e₀ + (1 - p₁)) ^ θ := h
        _ = (p₁ * e₀ + 1 - p₁) ^ θ := by ring_nf
    have hi' : (p₁ * u + 1 - p₁) ^ α ≤ (c₂ ^ α) ^ θ := by
      have h0 : 0 ≤ p₁ * u + 1 - p₁ := by nlinarith
      calc (p₁ * u + 1 - p₁) ^ α ≤ (c₂ ^ θ) ^ α := Real.rpow_le_rpow h0 hi hα.le
        _ = c₂ ^ (θ * α) := by rw [← Real.rpow_mul hc₂0]
        _ = (c₂ ^ α) ^ θ := by rw [mul_comm, Real.rpow_mul hc₂0]
    have hL0 : 0 ≤ 1 - p + p * u ^ (-α) := by
      have := Real.rpow_nonneg hu0.le (-α); nlinarith
    calc (1 - p + p * u ^ (-α)) * (p₁ * u + 1 - p₁) ^ α
        ≤ c₁ ^ θ * (c₂ ^ α) ^ θ :=
          mul_le_mul hii hi' (Real.rpow_nonneg (by nlinarith) _) (Real.rpow_nonneg hc₁0 _)
      _ = (c₁ * c₂ ^ α) ^ θ := by rw [Real.mul_rpow hc₁0 (Real.rpow_nonneg hc₂0 _)]
      _ ≤ max 1 (c₁ * c₂ ^ α) := by
          rcases le_or_gt (c₁ * c₂ ^ α) 1 with hc | hc
          · exact le_trans (Real.rpow_le_one hc0 hc hθ0) (le_max_left _ _)
          · calc (c₁ * c₂ ^ α) ^ θ ≤ (c₁ * c₂ ^ α) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hc.le hθ1
              _ = c₁ * c₂ ^ α := Real.rpow_one _
              _ ≤ _ := le_max_right _ _

/-- Case 1 (real form): `a ≤ b e^{-t/α}`. -/
lemma caseA (p p₁ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ p₁) (hq1 : p₁ ≤ 1)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a ≤ b * Real.exp (-t / α)) :
    (1 - p + p * Real.exp t) * (p₁ * a + (1 - p₁) * b) ^ α ≤ aConst α t p p₁ * b ^ α := by
  set e₀ : ℝ := Real.exp (-t / α) with he₀
  have he₀pos : 0 < e₀ := Real.exp_pos _
  have hD0 : 0 ≤ p₁ * a + (1 - p₁) * b := by nlinarith
  have hD : p₁ * a + (1 - p₁) * b ≤ b * (p₁ * e₀ + 1 - p₁) := by nlinarith
  have hc₂0 : 0 ≤ p₁ * e₀ + 1 - p₁ := by nlinarith
  have hc₁0 : 0 ≤ 1 - p + p * Real.exp t := by have := Real.exp_pos t; nlinarith
  calc (1 - p + p * Real.exp t) * (p₁ * a + (1 - p₁) * b) ^ α
      ≤ (1 - p + p * Real.exp t) * (b * (p₁ * e₀ + 1 - p₁)) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hD0 hD hα.le) hc₁0
    _ = ((1 - p + p * Real.exp t) * (p₁ * e₀ + 1 - p₁) ^ α) * b ^ α := by
        rw [Real.mul_rpow hb.le hc₂0]; ring
    _ ≤ aConst α t p p₁ * b ^ α := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hb.le _)
        exact le_max_right _ _

/-- Case 2 (real form): `b e^{-t/α} ≤ a ≤ b`, `a > 0`. -/
lemma caseB (p p₁ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ p₁) (hq1 : p₁ ≤ 1)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hba : b * Real.exp (-t / α) ≤ a) :
    ((1 - p) / b ^ α + p / a ^ α) * (p₁ * a + (1 - p₁) * b) ^ α ≤ aConst α t p p₁ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set u : ℝ := a / b with hu
  have hu0 : 0 < u := div_pos ha hb
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hb]; exact hab
  have hue : Real.exp (-t / α) ≤ u := by rw [hu, le_div_iff₀ hb]; linarith
  have hau : a = u * b := by rw [hu]; field_simp
  have key := keyF p p₁ hp0 hp1 hq0 hq1 α hα t ht u hu0 hu1 hue
  have hbα : 0 < b ^ α := Real.rpow_pos_of_pos hb _
  have huα : 0 < u ^ α := Real.rpow_pos_of_pos hu0 _
  have hD0 : 0 ≤ p₁ * u + 1 - p₁ := by nlinarith
  have h1 : (1 - p) / b ^ α + p / a ^ α = (1 - p + p * u ^ (-α)) / b ^ α := by
    rw [hau, Real.mul_rpow hu0.le hb.le, Real.rpow_neg hu0.le]
    field_simp
  have h2 : (p₁ * a + (1 - p₁) * b) ^ α = (p₁ * u + 1 - p₁) ^ α * b ^ α := by
    rw [hau, show p₁ * (u * b) + (1 - p₁) * b = (p₁ * u + 1 - p₁) * b by ring,
      Real.mul_rpow hD0 hb.le]
  rw [h1, h2]
  calc (1 - p + p * u ^ (-α)) / b ^ α * ((p₁ * u + 1 - p₁) ^ α * b ^ α)
      = (1 - p + p * u ^ (-α)) * (p₁ * u + 1 - p₁) ^ α := by field_simp
    _ ≤ _ := key

theorem lemma_2_3_5_core (p p₁ : unitInterval) (_hpp₁ : p < p₁)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ≥0∞) (hab : a ≤ b) (hb : b ≤ 1) :
    ENNReal.ofReal (1 - (p : ℝ)) / b ^ α
        + ENNReal.ofReal (p : ℝ) * min (1 / a ^ α) (ENNReal.ofReal (Real.exp t) / b ^ α)
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ))
          / (a * ENNReal.ofReal (p₁ : ℝ) + b * ENNReal.ofReal (1 - (p₁ : ℝ))) ^ α := by
  have hp0 : 0 ≤ (p:ℝ) := p.2.1
  have hp1 : (p:ℝ) ≤ 1 := p.2.2
  have hq0 : 0 ≤ (p₁:ℝ) := p₁.2.1
  have hq1 : (p₁:ℝ) ≤ 1 := p₁.2.2
  have haC1 : 1 ≤ aConst α t p p₁ := le_max_left _ _
  have haCpos : 0 < aConst α t p p₁ := by linarith
  have haCne : ENNReal.ofReal (aConst α t p p₁) ≠ 0 := (ENNReal.ofReal_pos.mpr haCpos).ne'
  rcases eq_or_ne b 0 with hb0 | hb0
  · have ha0 : a = 0 := nonpos_iff_eq_zero.mp (hb0 ▸ hab)
    subst hb0; subst ha0
    simp only [zero_mul, add_zero, ENNReal.zero_rpow_of_pos hα]
    rw [ENNReal.div_zero haCne]
    exact le_top
  have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top hbtop hab
  have hbE : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbtop).symm
  have haE : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hatop).symm
  have hb'pos : 0 < b.toReal := ENNReal.toReal_pos hb0 hbtop
  have ha'0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hab' : a.toReal ≤ b.toReal := ENNReal.toReal_mono hbtop hab
  generalize b.toReal = b' at hbE hb'pos hab'
  generalize a.toReal = a' at haE ha'0 hab'
  subst hbE; subst haE
  clear hb hab hb0 hbtop hatop
  set D : ℝ := a' * p₁ + b' * (1 - p₁) with hD
  have hD0 : 0 ≤ D := by nlinarith
  have hDE : ENNReal.ofReal a' * ENNReal.ofReal p₁ + ENNReal.ofReal b' * ENNReal.ofReal (1 - p₁)
      = ENNReal.ofReal D := by
    rw [hD, ← ENNReal.ofReal_mul ha'0, ← ENNReal.ofReal_mul hb'pos.le,
      ← ENNReal.ofReal_add (by positivity) (by nlinarith)]
  rw [hDE, ENNReal.ofReal_rpow_of_nonneg hD0 hα.le]
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · rw [← hD0', Real.zero_rpow hα.ne', ENNReal.ofReal_zero, ENNReal.div_zero haCne]
    exact le_top
  have hDα : 0 < D ^ α := Real.rpow_pos_of_pos hDpos _
  rw [← ENNReal.ofReal_div_of_pos hDα, ENNReal.ofReal_rpow_of_pos hb'pos]
  have hbα : 0 < b' ^ α := Real.rpow_pos_of_pos hb'pos _
  have h1p : 0 ≤ 1 - (p:ℝ) := by linarith
  rcases le_or_gt a' (b' * Real.exp (-t/α)) with hcase | hcase
  · -- case A
    calc _ ≤ ENNReal.ofReal (1 - p) / ENNReal.ofReal (b'^α)
          + ENNReal.ofReal p * (ENNReal.ofReal (Real.exp t) / ENNReal.ofReal (b'^α)) := by
          gcongr; exact min_le_right _ _
      _ = ENNReal.ofReal ((1 - p + p * Real.exp t) / b'^α) := by
          rw [← ENNReal.ofReal_div_of_pos hbα, ← ENNReal.ofReal_div_of_pos hbα,
            ← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (aConst α t p p₁ / D^α) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_div_iff₀ hbα hDα]
          have := caseA p p₁ hp0 hp1 hq0 hq1 α hα t ht a' b' ha'0 hb'pos hcase
          have hD' : (p₁:ℝ) * a' + (1 - p₁) * b' = D := by rw [hD]; ring
          rw [hD'] at this; exact this
  · -- case B
    have ha'pos : 0 < a' := lt_of_le_of_lt (by positivity) hcase
    have haα : 0 < a' ^ α := Real.rpow_pos_of_pos ha'pos _
    rw [ENNReal.ofReal_rpow_of_pos ha'pos]
    calc _ ≤ ENNReal.ofReal (1 - p) / ENNReal.ofReal (b'^α)
          + ENNReal.ofReal p * (1 / ENNReal.ofReal (a'^α)) := by
          gcongr; exact min_le_left _ _
      _ = ENNReal.ofReal ((1 - p) / b'^α + p / a'^α) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos hbα,
            ENNReal.ofReal_div_of_pos haα]
          simp [div_eq_mul_inv]
      _ ≤ ENNReal.ofReal (aConst α t p p₁ / D^α) := by
          apply ENNReal.ofReal_le_ofReal
          rw [le_div_iff₀ hDα]
          have := caseB p p₁ hp0 hp1 hq0 hq1 α hα t ht a' b' ha'pos hab' hcase.le
          have hD' : (p₁:ℝ) * a' + (1 - p₁) * b' = D := by rw [hD]; ring
          rw [hD'] at this; exact this


open Classical
open TalagrandConc.OnePoint (expMul)

/-! ### Weights -/

noncomputable def wB (p : unitInterval) (b : Bool) : ℝ≥0∞ :=
  ((cond b (unitInterval.toNNReal p) (1 - unitInterval.toNNReal p) : ℝ≥0) : ℝ≥0∞)

noncomputable def WB (N : ℕ) (p : unitInterval) (x : Fin N → Bool) : ℝ≥0∞ := ∏ i, wB p (x i)

lemma wB_true (p : unitInterval) : wB p true = ENNReal.ofReal p := by
  rw [ENNReal.ofReal_eq_coe_nnreal p.2.1]; rfl

lemma wB_false (p : unitInterval) : wB p false = ENNReal.ofReal (1 - p) := by
  have h : (0:ℝ) ≤ 1 - p := by linarith [p.2.2]
  rw [ENNReal.ofReal_eq_coe_nnreal h]
  simp only [wB, cond]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_sub (by exact_mod_cast p.2.2)]
  rfl

lemma wB_add (p : unitInterval) : wB p false + wB p true = 1 := by
  rw [wB_true, wB_false, ← ENNReal.ofReal_add (by linarith [p.2.2]) p.2.1]; simp

lemma WB_cons (N : ℕ) (p : unitInterval) (b : Bool) (y : Fin N → Bool) :
    WB (N+1) p (Fin.cons b y) = wB p b * WB N p y := by
  simp [WB, Fin.prod_univ_succ]

lemma sum_cons {M : Type*} [AddCommMonoid M] (N : ℕ) (g : (Fin (N+1) → Bool) → M) :
    ∑ x, g x = ∑ y, g (Fin.cons false y) + ∑ y, g (Fin.cons true y) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) (fun q => g (Fin.consEquiv _ q)) g
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

instance instProb (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (productMeasure N p) := by
  unfold productMeasure; infer_instance

lemma measure_singleton (N : ℕ) (p : unitInterval) (x : Fin N → Bool) :
    productMeasure N p {x} = WB N p x := by
  unfold productMeasure TalagrandCore.bernPi WB
  rw [← Set.univ_pi_singleton x, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  rfl

lemma lintegral_eq (N : ℕ) (p : unitInterval) (f : (Fin N → Bool) → ℝ≥0∞) :
    ∫⁻ x, f x ∂(productMeasure N p) = ∑ x, f x * WB N p x := by
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [measure_singleton]

noncomputable def M (N : ℕ) (p : unitInterval) (A : Set (Fin N → Bool)) : ℝ≥0∞ :=
  ∑ x, if x ∈ A then WB N p x else 0

lemma measure_eq (N : ℕ) (p : unitInterval) (A : Set (Fin N → Bool)) :
    productMeasure N p A = M N p A := by
  rw [← lintegral_indicator_one (by measurability), lintegral_eq]
  unfold M
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ A <;> simp [hx, Set.indicator]

lemma M_mono (N : ℕ) (p : unitInterval) {A B : Set (Fin N → Bool)} (h : A ⊆ B) :
    M N p A ≤ M N p B := by
  unfold M
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ A
  · simp [hx, h hx]
  · simp [hx]

lemma M_le_one (N : ℕ) (p : unitInterval) (A : Set (Fin N → Bool)) : M N p A ≤ 1 := by
  rw [← measure_eq]; exact prob_le_one

/-! ### Sections -/

def sec {N : ℕ} (b : Bool) (A : Set (Fin (N+1) → Bool)) : Set (Fin N → Bool) :=
  {y | Fin.cons b y ∈ A}

lemma M_succ (N : ℕ) (p : unitInterval) (A : Set (Fin (N+1) → Bool)) :
    M (N+1) p A = wB p false * M N p (sec false A) + wB p true * M N p (sec true A) := by
  unfold M
  rw [sum_cons]
  simp only [Finset.mul_sum, WB_cons]
  congr 1
  · apply Finset.sum_congr rfl; intro y _
    by_cases h : Fin.cons false y ∈ A <;> simp [sec, h]
  · apply Finset.sum_congr rfl; intro y _
    by_cases h : Fin.cons true y ∈ A <;> simp [sec, h]

/-! ### Distances -/

def cnt {N : ℕ} (x y : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true ∧ y i = false)).card

lemma dist_eq {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) :
    oneSidedDistToSet A x = ⨅ y ∈ A, (cnt x y : ℝ≥0∞) := by
  unfold oneSidedDistToSet cnt
  congr

lemma cnt_cons {N : ℕ} (b c : Bool) (y z : Fin N → Bool) :
    cnt (Fin.cons b y) (Fin.cons c z) = (if b = true ∧ c = false then 1 else 0) + cnt y z := by
  unfold cnt
  rw [Fin.card_filter_univ_succ']
  simp

lemma dist_le_of_mem {N : ℕ} (A : Set (Fin N → Bool)) (x y : Fin N → Bool) (hy : y ∈ A) :
    oneSidedDistToSet A x ≤ cnt x y := by
  rw [dist_eq]; exact iInf₂_le y hy

lemma le_dist {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) (c : ℝ≥0∞)
    (h : ∀ y ∈ A, c ≤ cnt x y) : c ≤ oneSidedDistToSet A x := by
  rw [dist_eq]; exact le_iInf₂ h

lemma dist_cons_false {N : ℕ} (A : Set (Fin (N+1) → Bool)) (y : Fin N → Bool) :
    oneSidedDistToSet A (Fin.cons false y) ≤ oneSidedDistToSet (sec false A ∪ sec true A) y := by
  apply le_dist; intro z hz
  rcases hz with hz | hz
  · calc _ ≤ (cnt (Fin.cons false y) (Fin.cons false z) : ℝ≥0∞) := dist_le_of_mem _ _ _ hz
      _ = cnt y z := by rw [cnt_cons]; simp
  · calc _ ≤ (cnt (Fin.cons false y) (Fin.cons true z) : ℝ≥0∞) := dist_le_of_mem _ _ _ hz
      _ = cnt y z := by rw [cnt_cons]; simp

lemma dist_cons_true_1 {N : ℕ} (A : Set (Fin (N+1) → Bool)) (y : Fin N → Bool) :
    oneSidedDistToSet A (Fin.cons true y) ≤ oneSidedDistToSet (sec true A) y := by
  apply le_dist; intro z hz
  calc _ ≤ (cnt (Fin.cons true y) (Fin.cons true z) : ℝ≥0∞) := dist_le_of_mem _ _ _ hz
    _ = cnt y z := by rw [cnt_cons]; simp

lemma dist_cons_true_2 {N : ℕ} (A : Set (Fin (N+1) → Bool)) (y : Fin N → Bool) :
    oneSidedDistToSet A (Fin.cons true y)
      ≤ 1 + oneSidedDistToSet (sec false A ∪ sec true A) y := by
  rw [dist_eq (sec false A ∪ sec true A)]
  simp_rw [ENNReal.add_iInf]
  refine le_iInf₂ fun z hz => ?_
  rcases hz with hz | hz
  · calc _ ≤ (cnt (Fin.cons true y) (Fin.cons false z) : ℝ≥0∞) := dist_le_of_mem _ _ _ hz
      _ = 1 + cnt y z := by rw [cnt_cons]; simp
  · calc _ ≤ (cnt (Fin.cons true y) (Fin.cons true z) : ℝ≥0∞) := dist_le_of_mem _ _ _ hz
      _ ≤ 1 + cnt y z := by rw [cnt_cons]; simp

/-! ### The exponential integrand -/

lemma expMul_eq (t : ℝ) (ht : 0 ≤ t) (z : ℝ≥0∞) :
    expMul t z = EReal.exp (((ENNReal.ofReal t * z : ℝ≥0∞)) : EReal) := by
  unfold expMul
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ht]

lemma expMul_mono (t : ℝ) (ht : 0 ≤ t) {z₁ z₂ : ℝ≥0∞} (h : z₁ ≤ z₂) :
    expMul t z₁ ≤ expMul t z₂ := by
  rw [expMul_eq t ht, expMul_eq t ht]
  apply EReal.exp_monotone
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact mul_le_mul' le_rfl h

lemma expMul_add_one (t : ℝ) (ht : 0 ≤ t) (z : ℝ≥0∞) :
    expMul t (1 + z) = ENNReal.ofReal (Real.exp t) * expMul t z := by
  rw [expMul_eq t ht, expMul_eq t ht, mul_add, mul_one, EReal.coe_ennreal_add, EReal.exp_add,
    EReal.coe_ennreal_ofReal, max_eq_left ht, EReal.exp_coe]

lemma expMul_zero' (t : ℝ) : expMul t 0 = 1 := by
  unfold expMul
  simp

/-! ### The main induction -/

noncomputable def S (N : ℕ) (p : unitInterval) (t : ℝ) (A : Set (Fin N → Bool)) : ℝ≥0∞ :=
  ∑ x, expMul t (oneSidedDistToSet A x) * WB N p x

lemma M_empty (N : ℕ) (p : unitInterval) : M N p (∅ : Set (Fin N → Bool)) = 0 := by
  simp [M]

theorem main (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (N : ℕ) (A : Set (Fin N → Bool)),
      S N p t A ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ)) ^ N / (M N p₁ A) ^ α := by
  have haC1 : 1 ≤ aConst α t p p₁ := le_max_left _ _
  have ha0 : ENNReal.ofReal (aConst α t p p₁) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  set a : ℝ≥0∞ := ENNReal.ofReal (aConst α t p p₁) with ha
  intro N
  induction N with
  | zero =>
    intro A
    rcases Set.eq_empty_or_nonempty A with hA | ⟨y, hy⟩
    · subst hA
      rw [M_empty, ENNReal.zero_rpow_of_pos hα, ENNReal.div_zero (pow_ne_zero _ ha0)]
      exact le_top
    · have hS : S 0 p t A ≤ 1 := by
        unfold S
        rw [Fintype.sum_unique]
        have hd : ∀ x, oneSidedDistToSet A x = 0 := by
          intro x
          apply le_antisymm _ bot_le
          have := dist_le_of_mem A x y hy
          simpa [cnt] using this
        rw [hd, expMul_zero']
        simp [WB]
      have hR : 1 ≤ a ^ 0 / (M 0 p₁ A) ^ α := by
        rw [pow_zero, ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top),
          one_mul]
        calc (M 0 p₁ A) ^ α ≤ (1 : ℝ≥0∞) ^ α := ENNReal.rpow_le_rpow (M_le_one _ _ _) hα.le
          _ = 1 := ENNReal.one_rpow _
      exact hS.trans hR
  | succ N ih =>
    intro A
    set A₀ := sec false A with hA₀
    set A₁ := sec true A with hA₁
    set B := A₀ ∪ A₁ with hB
    have hmono : Monotone (fun x : ℝ≥0∞ => wB p true * x) := fun _ _ h => mul_le_mul' le_rfl h
    have hS : S (N+1) p t A ≤ wB p false * S N p t B
        + wB p true * min (S N p t A₁) (ENNReal.ofReal (Real.exp t) * S N p t B) := by
      unfold S
      rw [sum_cons]
      simp only [WB_cons]
      apply add_le_add
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro y _
        calc expMul t (oneSidedDistToSet A (Fin.cons false y)) * (wB p false * WB N p y)
            = wB p false * (expMul t (oneSidedDistToSet A (Fin.cons false y)) * WB N p y) := by
              ring
          _ ≤ wB p false * (expMul t (oneSidedDistToSet B y) * WB N p y) := by
              gcongr
              exact expMul_mono t ht (dist_cons_false A y)
      · rw [hmono.map_min]
        apply le_min
        · rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y _
          calc expMul t (oneSidedDistToSet A (Fin.cons true y)) * (wB p true * WB N p y)
              = wB p true * (expMul t (oneSidedDistToSet A (Fin.cons true y)) * WB N p y) := by
                ring
            _ ≤ wB p true * (expMul t (oneSidedDistToSet A₁ y) * WB N p y) := by
                gcongr
                exact expMul_mono t ht (dist_cons_true_1 A y)
        · rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y _
          calc expMul t (oneSidedDistToSet A (Fin.cons true y)) * (wB p true * WB N p y)
              = wB p true * (expMul t (oneSidedDistToSet A (Fin.cons true y)) * WB N p y) := by
                ring
            _ ≤ wB p true * (expMul t (1 + oneSidedDistToSet B y) * WB N p y) := by
                gcongr
                exact expMul_mono t ht (dist_cons_true_2 A y)
            _ = wB p true * (ENNReal.ofReal (Real.exp t) *
                  (expMul t (oneSidedDistToSet B y) * WB N p y)) := by
                rw [expMul_add_one t ht]; ring
    have h1 := ih B
    have h2 := ih A₁
    have hA₁B : M N p₁ A₁ ≤ M N p₁ B := M_mono _ _ Set.subset_union_right
    have hA₀B : M N p₁ A₀ ≤ M N p₁ B := M_mono _ _ Set.subset_union_left
    have key := lemma_2_3_5_core p p₁ hpp₁ α hα t ht (M N p₁ A₁) (M N p₁ B) hA₁B (M_le_one _ _ _)
    calc S (N+1) p t A
        ≤ wB p false * S N p t B
          + wB p true * min (S N p t A₁) (ENNReal.ofReal (Real.exp t) * S N p t B) := hS
      _ ≤ wB p false * (a ^ N / (M N p₁ B) ^ α)
          + wB p true * min (a ^ N / (M N p₁ A₁) ^ α)
              (ENNReal.ofReal (Real.exp t) * (a ^ N / (M N p₁ B) ^ α)) := by
          gcongr
      _ ≤ a ^ N * (ENNReal.ofReal (1 - (p : ℝ)) / (M N p₁ B) ^ α
          + ENNReal.ofReal (p : ℝ) * min (1 / (M N p₁ A₁) ^ α)
              (ENNReal.ofReal (Real.exp t) / (M N p₁ B) ^ α)) := by
          rw [mul_add]
          apply add_le_add
          · apply le_of_eq
            rw [wB_false, div_eq_mul_inv, div_eq_mul_inv]; ring
          · rw [wB_true, show a ^ N * (ENNReal.ofReal (p : ℝ) * min (1 / (M N p₁ A₁) ^ α)
                (ENNReal.ofReal (Real.exp t) / (M N p₁ B) ^ α))
                = ENNReal.ofReal (p : ℝ) * (a ^ N * min (1 / (M N p₁ A₁) ^ α)
                (ENNReal.ofReal (Real.exp t) / (M N p₁ B) ^ α)) by ring]
            apply mul_le_mul' le_rfl
            have hmono' : Monotone (fun x : ℝ≥0∞ => a ^ N * x) := fun _ _ h => mul_le_mul' le_rfl h
            rw [hmono'.map_min]
            apply min_le_min
            · apply le_of_eq; simp only [div_eq_mul_inv, one_mul]
            · apply le_of_eq; simp only [div_eq_mul_inv]; ring
      _ ≤ a ^ N * (a / (M N p₁ A₁ * ENNReal.ofReal (p₁ : ℝ)
            + M N p₁ B * ENNReal.ofReal (1 - (p₁ : ℝ))) ^ α) := by
          gcongr
      _ = a ^ (N+1) / (M N p₁ A₁ * ENNReal.ofReal (p₁ : ℝ)
            + M N p₁ B * ENNReal.ofReal (1 - (p₁ : ℝ))) ^ α := by
          rw [pow_succ, mul_div_assoc]
      _ ≤ a ^ (N+1) / (M (N+1) p₁ A) ^ α := by
          apply ENNReal.div_le_div_left
          apply ENNReal.rpow_le_rpow _ hα.le
          rw [M_succ, wB_true, wB_false]
          calc ENNReal.ofReal (1 - (p₁ : ℝ)) * M N p₁ A₀ + ENNReal.ofReal (p₁ : ℝ) * M N p₁ A₁
              ≤ ENNReal.ofReal (1 - (p₁ : ℝ)) * M N p₁ B + ENNReal.ofReal (p₁ : ℝ) * M N p₁ A₁ := by
                gcongr
            _ = _ := by ring

theorem thm_2_3_4_core (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (N : ℕ) (A : Set (Fin N → Bool)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (oneSidedDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ)) ^ N / (productMeasure N p₁ A) ^ α := by
  rw [lintegral_eq, measure_eq]
  exact main p p₁ hpp₁ α hα t ht N A

end TalagrandConc.TwoPoint

open TalagrandConc.TwoPoint


theorem solution (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (N : ℕ) (A : Set (Fin N → Bool)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (oneSidedDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ)) ^ N / (productMeasure N p₁ A) ^ α := by
  exact thm_2_3_4_core p p₁ hpp₁ N A α hα t ht
