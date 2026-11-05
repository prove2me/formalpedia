-- Prove2me | solution 1 for WassFSG.Lip.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:20:42.041647+00:00
-- url     : https://prove2.me/submissions/d2f64bea-7f34-43f4-8f78-de4af65d7bcd

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSGL7Aux

set_option linter.unusedSectionVars false

/-- Coercion `ℝ → EReal` commutes with finite sums. -/
lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- `toENNReal` commutes with finite sums of nonnegative terms. -/
lemma toENNReal_sum {ι : Type*} (s : Finset ι) (f : ι → EReal) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ s, f i).toENNReal = ∑ i ∈ s, (f i).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      EReal.toENNReal_add (hf a) (Finset.sum_nonneg (fun i _ => hf i)), ih]

/-- Flipping all signs. -/
def negEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ i := !σ i
  invFun σ i := !σ i
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

lemma signVal_not (b : Bool) : WassFSG.Lip.signVal (!b) = - WassFSG.Lip.signVal b := by
  cases b <;> simp [WassFSG.Lip.signVal]

/-- An odd function of the sign vector sums to zero. -/
lemma sum_odd {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ σ, f (fun i => !σ i) = - f σ) :
    ∑ σ, f σ = 0 := by
  have h := Equiv.sum_comp (negEquiv n) f
  have h2 : ∑ σ, f ((negEquiv n) σ) = - ∑ σ, f σ := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun σ _ => hf σ)
  linarith

lemma rad_term_odd {Z : Type*} {n : ℕ} (g : Z → ℝ) (y : Fin n → Z) (σ : Fin n → Bool) :
    (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal ((fun i => !σ i) i) * g (y i) =
      - ((1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * g (y i)) := by
  simp only [signVal_not, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- Pointwise inequality used to pass from `S ≤ S' + ℓ` to positive/negative parts. -/
lemma parts_le (s s' : EReal) (l : ℝ) (hs' : 0 ≤ s') (h : s ≤ s' + l) :
    s.toENNReal + ENNReal.ofReal (-l) ≤
      (s'.toENNReal + ENNReal.ofReal l) + (-s).toENNReal := by
  induction s' using EReal.rec with
  | bot => exact absurd hs' (by simp)
  | top => simp
  | coe s' =>
    induction s using EReal.rec with
    | bot => simp
    | top => exact absurd h (by rw [top_le_iff, ← EReal.coe_add]; exact EReal.coe_ne_top _)
    | coe s =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
      have hs'0 : 0 ≤ s' := by exact_mod_cast hs'
      rw [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
        EReal.real_coe_toENNReal]
      have key : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
        intro x
        rcases le_total x 0 with hx | hx
        · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
        · rw [max_eq_left hx]
      rw [key s, key (-l), key l, key (-s), ← ENNReal.ofReal_add (le_max_right _ _)
        (le_max_right _ _), ← ENNReal.ofReal_add hs'0 (le_max_right _ _),
        ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases le_total s 0 with h1 | h1 <;> rcases le_total l 0 with h2 | h2 <;>
        simp only [max_eq_left, max_eq_right, h1, h2, neg_nonneg, neg_nonpos] <;> linarith

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

lemma continuous_empMean {n : ℕ} (h : Z → ℝ) (hc : Continuous h) :
    Continuous (fun z : Fin n → Z => WassFSG.Lip.empMean z h) := by
  unfold WassFSG.Lip.empMean
  fun_prop

lemma integrable_empMean {n : ℕ} (P : Measure Z) [IsProbabilityMeasure P] (h : Z → ℝ)
    (hi : Integrable h P) :
    Integrable (fun z : Fin n → Z => WassFSG.Lip.empMean z h) (Measure.pi fun _ => P) := by
  unfold WassFSG.Lip.empMean
  refine Integrable.const_mul ?_ _
  exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (i := i) hi)

lemma integral_empMean {n : ℕ} (hn : 0 < n) (P : Measure Z) [IsProbabilityMeasure P]
    (h : Z → ℝ) (hi : Integrable h P) :
    ∫ z, WassFSG.Lip.empMean z h ∂(Measure.pi fun _ : Fin n => P) = ∫ x, h x ∂P := by
  unfold WassFSG.Lip.empMean
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_comp_eval (i := i) hi),
    Finset.sum_congr rfl (fun i _ => integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
      hi.aestronglyMeasurable)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The coordinatewise swap of `(z, z')` on the coordinates where `σ i = false`. -/
def swapAt {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : Z × Z → Z × Z :=
  if σ i then id else Prod.swap

noncomputable def esw {n : ℕ} (σ : Fin n → Bool) :
    (Fin n → Z) × (Fin n → Z) → (Fin n → Z) × (Fin n → Z) :=
  (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)) ∘
    (fun a i => swapAt σ i (a i)) ∘ (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)).symm

lemma esw_mp {n : ℕ} (P : Measure Z) [IsProbabilityMeasure P] (σ : Fin n → Bool) :
    MeasurePreserving (esw (Z := Z) σ)
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => P))
      ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => P)) := by
  have hΦ := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n) (fun _ => P) (fun _ => P)
  have hsw : ∀ i, MeasurePreserving (swapAt (Z := Z) σ i) (P.prod P) (P.prod P) := by
    intro i
    unfold swapAt
    by_cases h : σ i
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h, if_false, Bool.false_eq_true]; exact Measure.measurePreserving_swap
  have hpi := measurePreserving_pi (fun _ : Fin n => P.prod P) (fun _ : Fin n => P.prod P) hsw
  exact hΦ.comp (hpi.comp hΦ.symm)

lemma esw_diff {n : ℕ} (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z)) (g : Z → ℝ) :
    WassFSG.Lip.empMean (esw σ p).2 g - WassFSG.Lip.empMean (esw σ p).1 g =
      (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * (g (p.2 i) - g (p.1 i)) := by
  unfold WassFSG.Lip.empMean
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [esw, swapAt, Function.comp, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, MeasurableEquiv.symm_mk, Equiv.arrowProdEquivProdArrow,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  cases σ i <;> simp [WassFSG.Lip.signVal]

end WassFSGL7Aux

open WassFSGL7Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (n : ℕ) (hn : 0 < n)
    (H : Set (Z → ℝ)) (hcont : ∀ h ∈ H, Continuous h) (hint : ∀ h ∈ H, Integrable h Ptrue) :
    ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
        (fun z => ⨆ h ∈ H, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal))
      ≤ 2 * WassFSG.Lip.expectedRad Ptrue n H := by
  classical
  set μ := Measure.pi fun _ : Fin n => Ptrue with hμ
  set ν := μ.prod μ with hν
  rcases Set.eq_empty_or_nonempty H with hHe | ⟨h0, hh0⟩
  · subst hHe
    unfold ModelRiskOT.Duality.extIntegral
    simp
  have hc0 := hcont h0 hh0
  have hi0 := hint h0 hh0
  -- notation
  let ℓ : (Fin n → Z) → ℝ := fun z => ∫ x, h0 x ∂Ptrue - WassFSG.Lip.empMean z h0
  let S : (Fin n → Z) → EReal := fun z => ⨆ h ∈ H, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal)
  let S' : (Fin n → Z) → EReal :=
    fun z => ⨆ h ∈ H, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h - ℓ z : ℝ) : EReal)
  let T' : (Fin n → Z) × (Fin n → Z) → EReal := fun p => ⨆ h ∈ H,
    ((WassFSG.Lip.empMean p.2 h - WassFSG.Lip.empMean p.1 h - (WassFSG.Lip.empMean p.2 h0 - WassFSG.Lip.empMean p.1 h0) : ℝ) : EReal)
  let A : (Fin n → Bool) → (Fin n → Z) → EReal := fun σ y => ⨆ g ∈ H,
    (((1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * g (y i) : ℝ) : EReal)
  -- nonnegativity
  have hS'0 : ∀ z, 0 ≤ S' z := fun z => le_iSup₂_of_le h0 hh0 (by simp [ℓ])
  have hT'0 : ∀ p, 0 ≤ T' p := fun p => le_iSup₂_of_le h0 hh0 (by simp)
  have hA0 : ∀ y, 0 ≤ ∑ σ, A σ y := by
    intro y
    have h1 : ∑ σ : Fin n → Bool, ((((1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * h0 (y i)
        : ℝ)) : EReal) ≤ ∑ σ, A σ y :=
      Finset.sum_le_sum (fun σ _ => le_iSup₂_of_le h0 hh0 le_rfl)
    rw [← coe_sum, sum_odd _ (fun σ => rad_term_odd h0 y σ)] at h1
    simpa using h1
  -- measurability (lower semicontinuity)
  have hSm : Measurable S := by
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_biSup (fun h hh => ?_))
    exact (continuous_coe_real_ereal.comp (continuous_const.sub
      (continuous_empMean h (hcont h hh)))).lowerSemicontinuous
  have hS'm : Measurable S' := by
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_biSup (fun h hh => ?_))
    exact (continuous_coe_real_ereal.comp ((continuous_const.sub
      (continuous_empMean h (hcont h hh))).sub (continuous_const.sub
        (continuous_empMean h0 hc0)))).lowerSemicontinuous
  have hT'm : Measurable T' := by
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_biSup (fun h hh => ?_))
    have c1 := continuous_empMean (n := n) h (hcont h hh)
    have c2 := continuous_empMean (n := n) h0 hc0
    exact (continuous_coe_real_ereal.comp (((c1.comp continuous_snd).sub
      (c1.comp continuous_fst)).sub ((c2.comp continuous_snd).sub
        (c2.comp continuous_fst)))).lowerSemicontinuous
  have hAm : ∀ σ, Measurable (A σ) := by
    intro σ
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_biSup (fun h hh => ?_))
    have hc := hcont h hh
    refine Continuous.lowerSemicontinuous ?_
    refine continuous_coe_real_ereal.comp ?_
    fun_prop
  have hSAm : Measurable (fun y => (∑ σ, A σ y).toENNReal) :=
    (Finset.measurable_sum _ (fun σ _ => hAm σ)).ereal_toENNReal
  -- Step 1 (Jensen): `S'⁺(z) ≤ ∫ T'⁺(z, ·)`
  have hjensen : ∀ z, (S' z).toENNReal ≤ ∫⁻ z', (T' (z, z')).toENNReal ∂μ := by
    intro z
    have : S' z ≤ ((∫⁻ z', (T' (z, z')).toENNReal ∂μ : ENNReal) : EReal) := by
      refine iSup₂_le (fun h hh => ?_)
      set g : (Fin n → Z) → ℝ := fun z' => WassFSG.Lip.empMean z' h - WassFSG.Lip.empMean z h - (WassFSG.Lip.empMean z' h0 - WassFSG.Lip.empMean z h0) with hg
      have hgi : Integrable g μ :=
        (((integrable_empMean Ptrue h (hint h hh)).sub (integrable_const _)).sub
          ((integrable_empMean Ptrue h0 hi0).sub (integrable_const _)))
      have i1 : Integrable (fun z' => WassFSG.Lip.empMean z' h) μ :=
        integrable_empMean Ptrue h (hint h hh)
      have i2 : Integrable (fun z' => WassFSG.Lip.empMean z' h0) μ :=
        integrable_empMean Ptrue h0 hi0
      have hgint : ∫ z', g z' ∂μ = ∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h - ℓ z := by
        have j1 : Integrable (fun z' => WassFSG.Lip.empMean z' h - WassFSG.Lip.empMean z h) μ :=
          i1.sub (integrable_const _)
        have j2 : Integrable (fun z' => WassFSG.Lip.empMean z' h0 - WassFSG.Lip.empMean z h0) μ :=
          i2.sub (integrable_const _)
        rw [hg]
        rw [integral_sub j1 j2,
          integral_sub i1 (integrable_const _), integral_sub i2 (integrable_const _),
          integral_empMean hn Ptrue h (hint h hh), integral_empMean hn Ptrue h0 hi0]
        simp [ℓ]
      rw [← hgint]
      have h1 : ∫ z', g z' ∂μ ≤ (∫⁻ z', ENNReal.ofReal (g z') ∂μ).toReal := by
        rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi]
        have := ENNReal.toReal_nonneg (a := ∫⁻ z', ENNReal.ofReal (-g z') ∂μ)
        linarith
      have hfin : ∫⁻ z', ENNReal.ofReal (g z') ∂μ ≠ ⊤ := hgi.lintegral_lt_top.ne
      have h2 : ∫⁻ z', ENNReal.ofReal (g z') ∂μ ≤ ∫⁻ z', (T' (z, z')).toENNReal ∂μ := by
        refine lintegral_mono (fun z' => ?_)
        rw [← EReal.real_coe_toENNReal]
        exact EReal.toENNReal_le_toENNReal (le_iSup₂_of_le h hh le_rfl)
      calc ((∫ z', g z' ∂μ : ℝ) : EReal)
          ≤ (((∫⁻ z', ENNReal.ofReal (g z') ∂μ).toReal : ℝ) : EReal) :=
            EReal.coe_le_coe_iff.2 h1
        _ = ((∫⁻ z', ENNReal.ofReal (g z') ∂μ : ENNReal) : EReal) :=
            EReal.coe_ennreal_toReal hfin
        _ ≤ _ := EReal.coe_ennreal_le_coe_ennreal_iff.2 h2
    simpa using EReal.toENNReal_le_toENNReal this
  have hstep1 : ∫⁻ z, (S' z).toENNReal ∂μ ≤ ∫⁻ p, (T' p).toENNReal ∂ν := by
    rw [hν, lintegral_prod _ hT'm.ereal_toENNReal.aemeasurable]
    exact lintegral_mono hjensen
  -- Step 2 (symmetrization): `Σ_σ T'⁺ ∘ e_σ ≤ (Σ_σ A_σ ∘ snd)⁺ + (Σ_σ A_σ ∘ fst)⁺`
  have hpt : ∀ p, ∑ σ : Fin n → Bool, (T' (esw σ p)).toENNReal ≤
      (∑ σ, A σ p.2).toENNReal + (∑ σ, A σ p.1).toENNReal := by
    intro p
    rw [← toENNReal_sum _ _ (fun σ => hT'0 _)]
    refine le_trans (EReal.toENNReal_le_toENNReal ?_) EReal.toENNReal_add_le
    let c : (Fin n → Bool) → ℝ := fun σ =>
      (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * (h0 (p.2 i) - h0 (p.1 i))
    have hterm : ∀ σ, T' (esw σ p) ≤ A σ p.2 + A (fun i => !σ i) p.1 + ((-c σ : ℝ) : EReal) := by
      intro σ
      refine iSup₂_le (fun h hh => ?_)
      rw [esw_diff σ p h, esw_diff σ p h0]
      have e : (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * (h (p.2 i) - h (p.1 i)) -
          (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * (h0 (p.2 i) - h0 (p.1 i)) =
          (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal (σ i) * h (p.2 i) +
          (1 / (n : ℝ)) * ∑ i, WassFSG.Lip.signVal ((fun i => !σ i) i) * h (p.1 i) + -c σ := by
        simp only [c, signVal_not, mul_sub, Finset.sum_sub_distrib, neg_mul,
          Finset.sum_neg_distrib]
        ring
      rw [e, EReal.coe_add, EReal.coe_add]
      exact add_le_add (add_le_add (le_iSup₂_of_le h hh le_rfl) (le_iSup₂_of_le h hh le_rfl))
        le_rfl
    refine le_trans (Finset.sum_le_sum (fun σ _ => hterm σ)) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← coe_sum]
    have hc0' : ∑ σ, -c σ = 0 := by
      refine sum_odd _ (fun σ => ?_)
      simp only [c, signVal_not, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]
    have hneg : ∑ σ : Fin n → Bool, A (fun i => !σ i) p.1 = ∑ σ, A σ p.1 :=
      Equiv.sum_comp (negEquiv n) (fun σ => A σ p.1)
    rw [hc0', hneg, EReal.coe_zero, add_zero]
  -- integrate
  set X := ∫⁻ p, (T' p).toENNReal ∂ν with hX
  set Y := ∫⁻ y, (∑ σ, A σ y).toENNReal ∂μ with hY
  have hcount : (2 : ENNReal) ^ n * X ≤ 2 * Y := by
    have h1 : ∀ σ : Fin n → Bool, ∫⁻ p, (T' (esw σ p)).toENNReal ∂ν = X := by
      intro σ
      exact (esw_mp Ptrue σ).lintegral_comp hT'm.ereal_toENNReal
    have h2 : ∑ σ : Fin n → Bool, ∫⁻ p, (T' (esw σ p)).toENNReal ∂ν = (2 : ENNReal) ^ n * X := by
      simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [← h2, ← lintegral_finsetSum _ (fun σ _ =>
      (show Measurable (fun p => (T' (esw σ p)).toENNReal) from
        (hT'm.comp (esw_mp Ptrue σ).measurable).ereal_toENNReal))]
    refine le_trans (lintegral_mono hpt) ?_
    have m2 : Measurable (fun p : (Fin n → Z) × (Fin n → Z) => (∑ σ, A σ p.2).toENNReal) :=
      hSAm.comp measurable_snd
    have m1 : Measurable (fun p : (Fin n → Z) × (Fin n → Z) => (∑ σ, A σ p.1).toENNReal) :=
      hSAm.comp measurable_fst
    rw [lintegral_add_left m2, hν, lintegral_prod _ m2.aemeasurable,
      lintegral_prod _ m1.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [two_mul]
  have hRad : ∫⁻ z, (WassFSG.Lip.radComp H z).toENNReal ∂μ = ((2 : ENNReal) ^ n)⁻¹ * Y := by
    have : ∀ z : Fin n → Z, (WassFSG.Lip.radComp H z).toENNReal =
        ((2 : ENNReal) ^ n)⁻¹ * (∑ σ, A σ z).toENNReal := by
      intro z
      unfold WassFSG.Lip.radComp
      rw [EReal.toENNReal_mul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)),
        EReal.real_coe_toENNReal, one_div, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    simp_rw [this]
    rw [lintegral_const_mul _ hSAm]
  have hRad0 : ∀ z : Fin n → Z, 0 ≤ WassFSG.Lip.radComp H z := by
    intro z
    unfold WassFSG.Lip.radComp
    exact EReal.mul_nonneg (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)) (hA0 z)
  have hexpRad : WassFSG.Lip.expectedRad Ptrue n H =
      ((∫⁻ z, (WassFSG.Lip.radComp H z).toENNReal ∂μ : ENNReal) : EReal) := by
    unfold WassFSG.Lip.expectedRad ModelRiskOT.Duality.extIntegral
    have : (fun z : Fin n → Z => (-WassFSG.Lip.radComp H z).toENNReal) = fun _ => 0 := by
      funext z; exact EReal.toENNReal_of_nonpos (by simpa using hRad0 z)
    rw [this, lintegral_zero]
    simp [hμ]
  have hfin2 : (2 : ENNReal) ^ n ≠ 0 := by simp
  have hfin2' : (2 : ENNReal) ^ n ≠ ⊤ := by simp
  have hXle : X ≤ 2 * ∫⁻ z, (WassFSG.Lip.radComp H z).toENNReal ∂μ := by
    rw [hRad]
    calc X = ((2 : ENNReal) ^ n)⁻¹ * ((2 : ENNReal) ^ n * X) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hfin2 hfin2', one_mul]
      _ ≤ ((2 : ENNReal) ^ n)⁻¹ * (2 * Y) := by gcongr
      _ = 2 * (((2 : ENNReal) ^ n)⁻¹ * Y) := by ring
  -- Step 3: from `S'` back to `S`
  have hSS' : ∀ z, S z ≤ S' z + ((ℓ z : ℝ) : EReal) := by
    intro z
    refine iSup₂_le (fun h hh => ?_)
    have : ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal) =
        ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h - ℓ z : ℝ) : EReal) + ((ℓ z : ℝ) : EReal) := by
      rw [← EReal.coe_add]; ring_nf
    rw [this]
    exact add_le_add (le_iSup₂_of_le h hh le_rfl) le_rfl
  have hℓi : Integrable ℓ μ := (integrable_const _).sub (integrable_empMean Ptrue h0 hi0)
  have hℓm : Measurable ℓ := (continuous_const.sub (continuous_empMean h0 hc0)).measurable
  have hℓ0 : ∫ z, ℓ z ∂μ = 0 := by
    show ∫ z, (∫ x, h0 x ∂Ptrue - WassFSG.Lip.empMean z h0) ∂μ = 0
    rw [integral_sub (integrable_const _) (integrable_empMean Ptrue h0 hi0),
      integral_empMean hn Ptrue h0 hi0]
    simp
  have hℓpn : ∫⁻ z, ENNReal.ofReal (ℓ z) ∂μ = ∫⁻ z, ENNReal.ofReal (-ℓ z) ∂μ := by
    have := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hℓi
    rw [hℓ0] at this
    exact (ENNReal.toReal_eq_toReal_iff' hℓi.lintegral_lt_top.ne
      hℓi.neg.lintegral_lt_top.ne).1 (by simp only [Pi.neg_apply]; linarith)
  have hcfin : ∫⁻ z, ENNReal.ofReal (-ℓ z) ∂μ ≠ ⊤ := hℓi.neg.lintegral_lt_top.ne
  have hpos : ∫⁻ z, (S z).toENNReal ∂μ ≤ ∫⁻ z, (S' z).toENNReal ∂μ + ∫⁻ z, (-S z).toENNReal ∂μ := by
    have h1 : ∫⁻ z, ((S z).toENNReal + ENNReal.ofReal (-ℓ z)) ∂μ ≤
        ∫⁻ z, (((S' z).toENNReal + ENNReal.ofReal (ℓ z)) + (-S z).toENNReal) ∂μ :=
      lintegral_mono (fun z => parts_le _ _ _ (hS'0 z) (hSS' z))
    rw [lintegral_add_right _ (show Measurable (fun z => ENNReal.ofReal (-ℓ z)) from
        hℓm.neg.ennreal_ofReal),
      lintegral_add_left (show Measurable (fun z => (S' z).toENNReal + ENNReal.ofReal (ℓ z)) from
        hS'm.ereal_toENNReal.add hℓm.ennreal_ofReal),
      lintegral_add_right _ (show Measurable (fun z => ENNReal.ofReal (ℓ z)) from
        hℓm.ennreal_ofReal), hℓpn] at h1
    have h2 : ∫⁻ z, (S z).toENNReal ∂μ + ∫⁻ z, ENNReal.ofReal (-ℓ z) ∂μ ≤
        (∫⁻ z, (S' z).toENNReal ∂μ + ∫⁻ z, (-S z).toENNReal ∂μ) +
          ∫⁻ z, ENNReal.ofReal (-ℓ z) ∂μ := by
      refine le_trans h1 (le_of_eq ?_); ring
    exact (ENNReal.add_le_add_iff_right hcfin).1 h2
  -- conclusion
  show ModelRiskOT.Duality.extIntegral μ S ≤ _
  unfold ModelRiskOT.Duality.extIntegral
  refine EReal.sub_le_of_le_add ?_
  rw [hexpRad]
  calc ((∫⁻ z, (S z).toENNReal ∂μ : ENNReal) : EReal)
      ≤ ((∫⁻ z, (S' z).toENNReal ∂μ + ∫⁻ z, (-S z).toENNReal ∂μ : ENNReal) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 hpos
    _ ≤ ((2 * ∫⁻ z, (WassFSG.Lip.radComp H z).toENNReal ∂μ +
          ∫⁻ z, (-S z).toENNReal ∂μ : ENNReal) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 (by gcongr; exact hstep1.trans hXle)
    _ = 2 * ((∫⁻ z, (WassFSG.Lip.radComp H z).toENNReal ∂μ : ENNReal) : EReal) +
          ((∫⁻ z, (-S z).toENNReal ∂μ : ENNReal) : EReal) := by
        rw [EReal.coe_ennreal_add, EReal.coe_ennreal_mul]
        rfl
