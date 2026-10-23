-- Prove2me | solution 1 for RiskFunctionals.Conditional.condAVaR_properties
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:59:41.422815+00:00
-- url     : https://prove2.me/submissions/2cafb405-17f2-414d-b68c-c9453e0a95cc

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_ConditionalAVaR

open MeasureTheory RiskFunctionals.Conditional

noncomputable def caP : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance caP_prob : IsProbabilityMeasure caP := by
  unfold caP; infer_instance

theorem caP_single (b : Bool) : caP {b} = 1 / 2 := by
  simp [caP, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

theorem caP_real_single (b : Bool) : caP.real {b} = 1 / 2 := by
  rw [measureReal_def, caP_single]; norm_num

theorem ca_int (f : Bool → ℝ) : ∫ x, f x ∂caP = (f true + f false) / 2 := by
  rw [integral_fintype (memLp_one_iff_integrable.1 MemLp.of_discrete)]
  simp [caP_real_single]; ring

theorem ca_ae {p : Bool → Prop} (h : ∀ᵐ b ∂caP, p b) (b : Bool) : p b := by
  by_contra hb
  have h0 := ae_iff.1 h
  have : caP {b} = 0 := measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hb) h0
  rw [caP_single] at this; norm_num at this

noncomputable def caY : Lp ℝ 1 caP := MemLp.toLp (fun b : Bool => if b then (1:ℝ) else 0) MemLp.of_discrete

theorem caY_val (b : Bool) : caY b = if b then 1 else 0 := ca_ae (MemLp.coeFn_toLp _) b

theorem ca_zero_val {p : ENNReal} (b : Bool) : (0 : Lp ℝ p caP) b = 0 := ca_ae (Lp.coeFn_zero ℝ p caP) b

theorem ca_L1 (W : Lp ℝ 1 caP) (hW : ∀ b, W b = if b then 1 else 0) :
    IsConditionalAVaR ⊥ caP (1 / 2) W 0 := by
  intro B hB
  have hlhs : ((∫ ω in B, ((0 : lpMeas ℝ ℝ ⊥ 1 caP) : Lp ℝ 1 caP) ω ∂caP : ℝ) : EReal) = 0 := by
    have : ∀ ω, ((0 : lpMeas ℝ ℝ ⊥ 1 caP) : Lp ℝ 1 caP) ω = 0 := fun ω => by
      rw [ZeroMemClass.coe_zero]; exact ca_zero_val ω
    simp [this]
  rw [hlhs]
  apply le_antisymm
  · refine le_iInf₂ fun Z hZ => ?_
    have h1 := ca_ae hZ.1
    rw [ca_int]
    exact EReal.coe_nonneg.2 (by
      have a := (h1 true).1; have b := (h1 false).1
      rw [hW, hW]; simp only [if_true, Bool.false_eq_true, if_false]; nlinarith)
  · rcases MeasurableSpace.measurableSet_bot_iff.1 hB with rfl | rfl
    · refine le_trans (iInf₂_le (0 : Lp ℝ ⊤ caP) (And.intro ?_ ?_)) ?_
      · exact Filter.Eventually.of_forall fun ω => by simp [ca_zero_val]
      · refine Filter.Eventually.of_forall fun ω => ?_
        rw [condExp_bot']
        simp [ca_zero_val]
      · simp [ca_zero_val]
    · set Z : Lp ℝ ⊤ caP := MemLp.toLp (fun b : Bool => if b then (0:ℝ) else 2) MemLp.of_discrete
      have hZ : ∀ b, Z b = if b then 0 else 2 := fun b => ca_ae (MemLp.coeFn_toLp _) b
      refine le_trans (iInf₂_le Z (And.intro ?_ ?_)) ?_
      · exact Filter.Eventually.of_forall fun ω => by
          rw [hZ]; cases ω <;> norm_num
      · refine Filter.Eventually.of_forall fun ω => ?_
        rw [condExp_bot', ca_int, probReal_univ]
        simp [hZ]
      · rw [ca_int]; simp [hW, hZ]

theorem ca_mem : caY ∈ lpMeas ℝ ℝ (inferInstance : MeasurableSpace Bool) 1 caP :=
  Lp.aestronglyMeasurable caY

theorem ca_L2 : IsConditionalAVaR (inferInstance : MeasurableSpace Bool) caP (1 / 2) caY
    ⟨caY, ca_mem⟩ := by
  intro B hB
  have hval : ∀ Z : Lp ℝ ⊤ caP,
      caP[(Z : Bool → ℝ)|(inferInstance : MeasurableSpace Bool)] =ᵐ[caP] B.indicator (fun _ => (1:ℝ)) →
      ∫ ω, caY ω * Z ω ∂caP = ∫ ω in B, caY ω ∂caP := by
    intro Z hZ
    rw [condExp_of_stronglyMeasurable le_rfl (Lp.stronglyMeasurable Z)
      ((Lp.memLp Z).integrable le_top)] at hZ
    have hZp := ca_ae hZ
    rw [← integral_indicator hB]
    congr 1; funext ω; rw [hZp ω]
    by_cases h : ω ∈ B <;> simp [h]
  change ((∫ ω in B, caY ω ∂caP : ℝ) : EReal) = _
  apply le_antisymm
  · exact le_iInf₂ fun Z hZ => by rw [hval Z hZ.2]
  · set Z0 : Lp ℝ ⊤ caP := MemLp.toLp (B.indicator fun _ => (1:ℝ)) MemLp.of_discrete
    have hZ0 : (Z0 : Bool → ℝ) =ᵐ[caP] B.indicator fun _ => (1:ℝ) := MemLp.coeFn_toLp _
    have hc : caP[(Z0 : Bool → ℝ)|(inferInstance : MeasurableSpace Bool)] =ᵐ[caP]
        B.indicator (fun _ => (1:ℝ)) := by
      rw [condExp_of_stronglyMeasurable le_rfl (Lp.stronglyMeasurable Z0)
        ((Lp.memLp Z0).integrable le_top)]
      exact hZ0
    refine le_trans (iInf₂_le Z0 (And.intro ?_ hc)) (by rw [hval Z0 hc])
    filter_upwards [hZ0] with ω hω
    rw [hω]
    by_cases h : ω ∈ B <;> simp [h]

open RiskFunctionals.Conditional

theorem solution : ¬ (∀ {Ω : Type} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P] (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1),
    -- (i) version-independence (Definition 2.55): it is a function `Φ` of the conditional
    -- distribution function `G(·|ℱ₁)` of `Y` (a.s.), one `Φ` for every `Y`
    (∃ Φ : (ℝ → ℝ) → ℝ, ∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ m 1 P) (G : Ω → ℝ → ℝ),
      IsConditionalAVaR m P α Y V → IsConditionalDistributionFunction m P (Y : Ω → ℝ) G →
        ∀ᵐ ω ∂P, (V : Lp ℝ 1 P) ω = Φ (G ω)) ∧
    -- (i) it maps `L₁(ℱ)` to `L₁(ℱ₁)`: (2.57) has exactly one solution in `L₁(ℱ₁)`
    (∀ Y : Lp ℝ 1 P, ∃! V : lpMeas ℝ ℝ m 1 P, IsConditionalAVaR m P α Y V) ∧
    -- (ii) concavity with `ℱ₁`-measurable weights `0 ≤ Λ ≤ 1`
    (∀ Λ : Ω → ℝ, Measurable[m] Λ → (∀ᵐ ω ∂P, 0 ≤ Λ ω ∧ Λ ω ≤ 1) →
      ∀ (Y₁ Y₂ W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] (fun ω => Λ ω * Y₁ ω + (1 - Λ ω) * Y₂ ω) →
      ∀ (V₁ V₂ V : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y₁ V₁ →
        IsConditionalAVaR m P α Y₂ V₂ → IsConditionalAVaR m P α W V →
        ∀ᵐ ω ∂P, Λ ω * (V₁ : Lp ℝ 1 P) ω + (1 - Λ ω) * (V₂ : Lp ℝ 1 P) ω
          ≤ (V : Lp ℝ 1 P) ω) ∧
    -- (iii) homogeneity for non-negative bounded `ℱ₁`-measurable `Λ`
    (∀ Λ : Ω → ℝ, Measurable[m] Λ → (∀ᵐ ω ∂P, 0 ≤ Λ ω) → (∃ C : ℝ, ∀ᵐ ω ∂P, Λ ω ≤ C) →
      ∀ (Y W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] (fun ω => Λ ω * Y ω) →
      ∀ (V V' : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y V → IsConditionalAVaR m P α W V' →
        ∀ᵐ ω ∂P, (V' : Lp ℝ 1 P) ω = Λ ω * (V : Lp ℝ 1 P) ω) ∧
    -- (iv) monotonicity
    (∀ (Y₁ Y₂ : Lp ℝ 1 P), (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) →
      ∀ (V₁ V₂ : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α Y₁ V₁ →
        IsConditionalAVaR m P α Y₂ V₂ → ∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ (V₂ : Lp ℝ 1 P) ω) ∧
    -- (v) `Y ◁ ℱ₁` (`Y` has an `ℱ₁`-measurable version) implies `𝔸𝕍@ℝ_α(Y|ℱ₁) = Y`
    (∀ Y : Lp ℝ 1 P, Y ∈ lpMeas ℝ ℝ m 1 P →
      ∀ V : lpMeas ℝ ℝ m 1 P, IsConditionalAVaR m P α Y V →
        ((V : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] (Y : Ω → ℝ)) ∧
    -- (vi) for the trivial σ-field `ℱ₀ = {∅, Ω}` (`⊥`), `𝔸𝕍@ℝ_α(Y|ℱ₀) = 𝔸𝕍@ℝ_α(Y)`
    (∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ (⊥ : MeasurableSpace Ω) 1 P),
      IsConditionalAVaR ⊥ P α Y V →
        ∀ᵐ ω ∂P, (V : Lp ℝ 1 P) ω = averageValueAtRisk P (Y : Ω → ℝ) α) ∧
    -- (vii) monotonicity in the level: `α₁ ≤ α₂` implies `𝔸𝕍@ℝ_{α₁}(Y|ℱ₁) ≤ 𝔸𝕍@ℝ_{α₂}(Y|ℱ₁)`
    (∀ (α₁ α₂ : ℝ), 0 < α₁ → α₁ ≤ α₂ → α₂ ≤ 1 →
      ∀ (Y : Lp ℝ 1 P) (V₁ V₂ : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P α₁ Y V₁ →
        IsConditionalAVaR m P α₂ Y V₂ → ∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ (V₂ : Lp ℝ 1 P) ω) ∧
    -- (viii) `𝔸𝕍@ℝ₁(Y|ℱ₁) = 𝔼(Y|ℱ₁)`
    (∀ (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ m 1 P), IsConditionalAVaR m P 1 Y V →
      ((V : Lp ℝ 1 P) : Ω → ℝ) =ᵐ[P] P[(Y : Ω → ℝ)|m]) ∧
    -- (ix) (2.58) for `ℱ₁ ⊆ ℱ₂ ⊆ ℱ`: `𝔸𝕍@ℝ_α(Y|ℱ₁) ≤ 𝔼[𝔸𝕍@ℝ_α(Y|ℱ₂)|ℱ₁] ≤ 𝔸𝕍@ℝ_α(𝔼(Y|ℱ₂)|ℱ₁)`
    (∀ (Y : Lp ℝ 1 P) (V₁ V₃ : lpMeas ℝ ℝ m 1 P) (m₂ : MeasurableSpace Ω), m ≤ m₂ → m₂ ≤ mΩ →
      ∀ (W : Lp ℝ 1 P), (W : Ω → ℝ) =ᵐ[P] P[(Y : Ω → ℝ)|m₂] →
      ∀ V₂ : @lpMeas Ω ℝ ℝ _ _ _ m₂ mΩ 1 P,
        IsConditionalAVaR m P α Y V₁ → IsConditionalAVaR m₂ P α Y V₂ →
        IsConditionalAVaR m P α W V₃ →
        (∀ᵐ ω ∂P, (V₁ : Lp ℝ 1 P) ω ≤ P[((V₂ : Lp ℝ 1 P) : Ω → ℝ)|m] ω) ∧
          (∀ᵐ ω ∂P, P[((V₂ : Lp ℝ 1 P) : Ω → ℝ)|m] ω ≤ (V₃ : Lp ℝ 1 P) ω))) := by
  intro h
  have H := @h Bool ⊥ inferInstance bot_le caP caP_prob (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, -, h9⟩ := H
  have hW : (caY : Bool → ℝ) =ᵐ[caP] caP[(caY : Bool → ℝ)|(inferInstance : MeasurableSpace Bool)] := by
    rw [condExp_of_stronglyMeasurable le_rfl (Lp.stronglyMeasurable caY) (L1.integrable_coeFn caY)]
  have h2 := (h9 caY 0 0 inferInstance bot_le le_rfl caY hW ⟨caY, ca_mem⟩
    (ca_L1 caY caY_val) ca_L2 (ca_L1 caY caY_val)).2
  have h3 := ca_ae h2 true
  rw [condExp_bot', ca_int, probReal_univ, ZeroMemClass.coe_zero, ca_zero_val] at h3
  change (1:ℝ)⁻¹ • ((caY true + caY false) / 2) ≤ 0 at h3
  rw [caY_val, caY_val] at h3
  norm_num at h3
