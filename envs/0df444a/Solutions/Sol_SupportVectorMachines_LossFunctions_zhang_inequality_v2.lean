-- Prove2me | solution 1 for SupportVectorMachines.LossFunctions.zhang_inequality_v2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:56:38.462233+00:00
-- url     : https://prove2.me/submissions/15a3b6c4-2e8b-400f-8575-9b6978b3b421

/-
Zhang's inequality (Steinwart–Christmann, Theorem 2.31).

Proof route. Since `P` lives on `X × {-1, 1}` with `P(A × {1}) = ∫_A η dP_X`, it is the sum of the
two slice measures `η dP_X ⊗ δ₁` and `(1 - η) dP_X ⊗ δ₋₁` (`ZhangProof.disint`). Hence every risk
is `∫ ofReal (η L(x,1,f x) + (1-η) L(x,-1,f x)) dP_X`, the Bayes risks are the integrals of the
pointwise minima (`2 min(η,1-η)` for the hinge loss, `min(η,1-η)` for the classification loss, both
attained at `sgn(2η-1)`), the hinge excess risk of `f ∈ [-1,1]` is exactly `|f - f*| |2η - 1|`,
and the pointwise inequality `c + m ≤ h` gives the comparison of excess risks.
-/
import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses_v2

set_option autoImplicit false

open MeasureTheory

namespace ZhangProof

variable {X : Type*} [MeasurableSpace X]

/-- A probability measure on `X × ℝ` supported on `X × {-1, 1}` with conditional probability `η`
of the label `1` is the sum of two weighted copies of its marginal placed on the slices `y = 1`
and `y = -1`. -/
theorem disint (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ) (hη_meas : Measurable η)
    (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hη : ∀ A, MeasurableSet A →
      P (A ×ˢ ({1} : Set ℝ)) = ∫⁻ x in A, ENNReal.ofReal (η x) ∂(P.map Prod.fst))
    (G : X × ℝ → ENNReal) (hG : Measurable G) :
    ∫⁻ p, G p ∂P = ∫⁻ x, (ENNReal.ofReal (η x) * G (x, 1) +
      ENNReal.ofReal (1 - η x) * G (x, -1)) ∂(P.map Prod.fst) := by
  set PX : Measure X := P.map Prod.fst with hPX
  have : IsProbabilityMeasure PX := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  set S : Set (X × ℝ) := Set.univ ×ˢ ({-1, 1} : Set ℝ) with hS
  have hSmeas : MeasurableSet S :=
    MeasurableSet.univ.prod (Set.toFinite _).measurableSet
  have hSc : P Sᶜ = 0 := by
    rw [measure_compl hSmeas (by simp), hY]; simp
  have hf1 : Measurable (fun x : X => ENNReal.ofReal (η x)) := hη_meas.ennreal_ofReal
  have hf2 : Measurable (fun x : X => ENNReal.ofReal (1 - η x)) :=
    (measurable_const.sub hη_meas).ennreal_ofReal
  have hm1 : Measurable (fun x : X => (x, (1 : ℝ))) := measurable_id.prodMk measurable_const
  have hm2 : Measurable (fun x : X => (x, (-1 : ℝ))) := measurable_id.prodMk measurable_const
  -- slice masses
  have hone : ∀ A, MeasurableSet A → ∫⁻ x in A, ENNReal.ofReal (η x) ∂PX +
      ∫⁻ x in A, ENNReal.ofReal (1 - η x) ∂PX = PX A := by
    intro A hA
    rw [← lintegral_add_left hf1]
    have : ∀ x, ENNReal.ofReal (η x) + ENNReal.ofReal (1 - η x) = 1 := by
      intro x
      rw [← ENNReal.ofReal_add (hη01 x).1 (by linarith [(hη01 x).2])]
      simp
    simp [this]
  have hmarg : ∀ A, MeasurableSet A → P (A ×ˢ ({-1, 1} : Set ℝ)) = PX A := by
    intro A hA
    have e : PX A = P (Prod.fst ⁻¹' A) := Measure.map_apply measurable_fst hA
    have : Prod.fst ⁻¹' A ∩ S = A ×ˢ ({-1, 1} : Set ℝ) := by ext p; simp [hS]
    rw [e, ← this, measure_inter_conull hSc]
  have hmass : ∀ A, MeasurableSet A → P (A ×ˢ ({-1} : Set ℝ)) = ∫⁻ x in A, ENNReal.ofReal (1 - η x) ∂PX := by
    intro A hA
    have h1 : P (A ×ˢ ({-1, 1} : Set ℝ)) = PX A := hmarg A hA
    have h2 : P (A ×ˢ ({-1, 1} : Set ℝ)) = P (A ×ˢ ({1} : Set ℝ)) + P (A ×ˢ ({-1} : Set ℝ)) := by
      have : A ×ˢ ({-1, 1} : Set ℝ) = A ×ˢ ({1} : Set ℝ) ∪ A ×ˢ ({-1} : Set ℝ) := by
        ext p; simp; tauto
      rw [this, measure_union]
      · rw [Set.disjoint_left]
        intro p hp1 hp2
        simp at hp1 hp2
        linarith [hp1.2, hp2.2]
      · exact hA.prod (measurableSet_singleton _)
    have hfin : ∫⁻ x in A, ENNReal.ofReal (η x) ∂PX ≠ ⊤ := by
      refine ne_top_of_le_ne_top (measure_ne_top PX A) ?_
      rw [← hone A hA]; exact le_self_add
    have := hone A hA
    rw [← h1, h2, hη A hA] at this
    exact (ENNReal.add_right_inj hfin).mp this.symm
  -- the representing measure
  set Q : Measure (X × ℝ) :=
    (PX.withDensity fun x => ENNReal.ofReal (η x)).map (fun x => (x, (1 : ℝ))) +
    (PX.withDensity fun x => ENNReal.ofReal (1 - η x)).map (fun x => (x, (-1 : ℝ))) with hQ
  have hrect : ∀ A B : Set _, MeasurableSet A → MeasurableSet B → P (A ×ˢ B) = Q (A ×ˢ B) := by
    intro A B hA hB
    have hQ1 : Q (A ×ˢ B) =
        (PX.withDensity fun x => ENNReal.ofReal (η x)) ((fun x : X => (x, (1 : ℝ))) ⁻¹' (A ×ˢ B)) +
        (PX.withDensity fun x => ENNReal.ofReal (1 - η x))
          ((fun x : X => (x, (-1 : ℝ))) ⁻¹' (A ×ˢ B)) := by
      rw [hQ, Measure.add_apply, Measure.map_apply hm1 (hA.prod hB),
        Measure.map_apply hm2 (hA.prod hB)]
    have hP1 : P (A ×ˢ B) = P (A ×ˢ (B ∩ ({-1, 1} : Set ℝ))) := by
      have : A ×ˢ (B ∩ ({-1, 1} : Set ℝ)) = A ×ˢ B ∩ S := by
        ext p; simp [hS]; tauto
      rw [this, measure_inter_conull hSc]
    rw [hQ1, hP1]
    by_cases h1 : (1 : ℝ) ∈ B <;> by_cases h2 : (-1 : ℝ) ∈ B
    · have : B ∩ ({-1, 1} : Set ℝ) = {-1, 1} := by
        ext t; simp; intro ht; rcases ht with rfl | rfl <;> assumption
      have e1 : (fun x : X => (x, (1 : ℝ))) ⁻¹' (A ×ˢ B) = A := by ext x; simp [h1]
      have e2 : (fun x : X => (x, (-1 : ℝ))) ⁻¹' (A ×ˢ B) = A := by ext x; simp [h2]
      rw [this, e1, e2, withDensity_apply _ hA, withDensity_apply _ hA, hone A hA]
      exact hmarg A hA
    · have : B ∩ ({-1, 1} : Set ℝ) = {1} := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ht, rfl | rfl⟩
          · exact absurd ht h2
          · rfl
        · rintro rfl; exact ⟨h1, Or.inr rfl⟩
      have e1 : (fun x : X => (x, (1 : ℝ))) ⁻¹' (A ×ˢ B) = A := by ext x; simp [h1]
      have e2 : (fun x : X => (x, (-1 : ℝ))) ⁻¹' (A ×ˢ B) = ∅ := by ext x; simp [h2]
      rw [this, e1, e2, withDensity_apply _ hA, hη A hA]; simp
    · have : B ∩ ({-1, 1} : Set ℝ) = {-1} := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ht, rfl | rfl⟩
          · rfl
          · exact absurd ht h1
        · rintro rfl; exact ⟨h2, Or.inl rfl⟩
      have e1 : (fun x : X => (x, (1 : ℝ))) ⁻¹' (A ×ˢ B) = ∅ := by ext x; simp [h1]
      have e2 : (fun x : X => (x, (-1 : ℝ))) ⁻¹' (A ×ˢ B) = A := by ext x; simp [h2]
      rw [this, e1, e2, withDensity_apply _ hA, hmass A hA]; simp
    · have : B ∩ ({-1, 1} : Set ℝ) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro ht (rfl | rfl)
        · exact absurd ht h2
        · exact absurd ht h1
      have e1 : (fun x : X => (x, (1 : ℝ))) ⁻¹' (A ×ˢ B) = ∅ := by ext x; simp [h1]
      have e2 : (fun x : X => (x, (-1 : ℝ))) ⁻¹' (A ×ˢ B) = ∅ := by ext x; simp [h2]
      rw [this, e1, e2]; simp
  have hPQ : P = Q := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro s ⟨A, hA, B, hB, rfl⟩
      exact hrect A B hA hB
    · have := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      simpa using this
  have hg1 : Measurable (fun a : X => G (a, 1)) := hG.comp hm1
  have hg2 : Measurable (fun a : X => G (a, -1)) := hG.comp hm2
  rw [hPQ, hQ, lintegral_add_measure, lintegral_map hG hm1, lintegral_map hG hm2,
    lintegral_withDensity_eq_lintegral_mul _ hf1 hg1,
    lintegral_withDensity_eq_lintegral_mul _ hf2 hg2,
    ← lintegral_add_left (hf1.mul hg1)]
  rfl


/-! ### Pointwise real inequalities -/

/-- Conditional hinge risk at the prediction `t`. -/
noncomputable def hingeC (η t : ℝ) : ℝ := η * max 0 (1 - t) + (1 - η) * max 0 (1 + t)

/-- Conditional classification risk at the prediction `t`. -/
noncomputable def classC (η t : ℝ) : ℝ :=
  η * (if t < 0 then 1 else 0) + (1 - η) * (if t < 0 then 0 else 1)

theorem hinge_lower {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (t : ℝ) :
    2 * min η (1 - η) ≤ hingeC η t := by
  unfold hingeC
  have ha := le_max_right 0 (1 - t)
  have hb := le_max_right 0 (1 + t)
  have ha0 := le_max_left 0 (1 - t)
  have hb0 := le_max_left 0 (1 + t)
  set a := max 0 (1 - t)
  set b := max 0 (1 + t)
  rcases le_total η (1 - η) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg h0 (show 0 ≤ a + b - 2 by linarith),
      mul_nonneg (show 0 ≤ 1 - 2 * η by linarith) hb0]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (show 0 ≤ 1 - η by linarith) (show 0 ≤ a + b - 2 by linarith),
      mul_nonneg (show 0 ≤ 2 * η - 1 by linarith) ha0]

theorem class_lower {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (t : ℝ) :
    min η (1 - η) ≤ classC η t := by
  unfold classC
  by_cases ht : t < 0
  · simp [ht]
  · simp [ht]

theorem zhang_pointwise {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (t : ℝ) :
    classC η t + min η (1 - η) ≤ hingeC η t := by
  have hl := hinge_lower h0 h1 t
  unfold classC hingeC at *
  by_cases ht : t < 0
  · simp only [ht, if_true]
    rcases le_total η (1 - η) with h | h
    · rw [min_eq_left h] at hl ⊢
      nlinarith [hl]
    · rw [min_eq_right h]
      by_cases hm : -1 ≤ t
      · rw [max_eq_right (show (0:ℝ) ≤ 1 - t by linarith),
          max_eq_right (show (0:ℝ) ≤ 1 + t by linarith)]
        nlinarith [mul_nonneg (show 0 ≤ -t by linarith) (show 0 ≤ 2 * η - 1 by linarith)]
      · rw [max_eq_right (show (0:ℝ) ≤ 1 - t by linarith),
          max_eq_left (show 1 + t ≤ (0:ℝ) by linarith)]
        nlinarith
  · simp only [ht, if_false]
    rcases le_total η (1 - η) with h | h
    · rw [min_eq_left h]
      rw [max_eq_right (show (0:ℝ) ≤ 1 + t by linarith)]
      by_cases hm : t ≤ 1
      · rw [max_eq_right (show (0:ℝ) ≤ 1 - t by linarith)]
        nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ 1 - 2 * η by linarith)]
      · rw [max_eq_left (show 1 - t ≤ (0:ℝ) by linarith)]
        nlinarith
    · rw [min_eq_right h] at hl ⊢
      nlinarith [hl]

/-- For `|t| ≤ 1` the conditional hinge risk equals the minimum plus `|t - f*| |2η - 1|`. -/
theorem hinge_identity {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    hingeC η t = 2 * min η (1 - η) +
      |t - SupportVectorMachines.LossFunctions.sgn (2 * η - 1)| * |2 * η - 1| := by
  obtain ⟨htl, htu⟩ := ht
  unfold hingeC SupportVectorMachines.LossFunctions.sgn
  rw [max_eq_right (show (0:ℝ) ≤ 1 - t by linarith), max_eq_right (show (0:ℝ) ≤ 1 + t by linarith)]
  by_cases h : 2 * η - 1 < 0
  · simp only [h, if_true]
    rw [min_eq_left (by linarith), abs_of_neg h, abs_of_nonneg (by linarith : 0 ≤ t - -1)]
    ring
  · simp only [h, if_false]
    rw [min_eq_right (by linarith), abs_of_nonneg (by linarith : 0 ≤ 2 * η - 1),
      abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    ring

theorem hinge_at_bayes {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    hingeC η (SupportVectorMachines.LossFunctions.sgn (2 * η - 1)) = 2 * min η (1 - η) := by
  unfold hingeC SupportVectorMachines.LossFunctions.sgn
  by_cases h : 2 * η - 1 < 0
  · simp only [h, if_true]
    rw [min_eq_left (by linarith)]
    norm_num
    try ring
  · simp only [h, if_false]
    rw [min_eq_right (by linarith)]
    norm_num
    try ring

theorem class_at_bayes {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    classC η (SupportVectorMachines.LossFunctions.sgn (2 * η - 1)) = min η (1 - η) := by
  unfold classC SupportVectorMachines.LossFunctions.sgn
  by_cases h : 2 * η - 1 < 0
  · simp only [h, if_true]
    rw [min_eq_left (by linarith)]
    norm_num
  · simp only [h, if_false]
    rw [min_eq_right (by linarith)]
    norm_num


/-! ### Risks via conditional risks -/

open SupportVectorMachines.LossFunctions

/-- The standing hypotheses on `P` and its conditional probability `η`. -/
structure Setup (P : Measure (X × ℝ)) (η : X → ℝ) : Prop where
  hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1
  meas : Measurable η
  h01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1
  hη : ∀ A, MeasurableSet A →
    P (A ×ˢ ({1} : Set ℝ)) = ∫⁻ x in A, ENNReal.ofReal (η x) ∂(P.map Prod.fst)

/-- The conditional risk of `L` at the prediction `t` given `x`. -/
noncomputable def cond (L : Loss X) (η : X → ℝ) (x : X) (t : ℝ) : ℝ :=
  η x * L x 1 t + (1 - η x) * L x (-1) t

theorem risk_eq (L : Loss X) (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ}
    (hS : Setup P η) {f : X → ℝ} (hf : Measurable f) :
    risk L P f = ∫⁻ x, ENNReal.ofReal (cond L η x (f x)) ∂(P.map Prod.fst) := by
  unfold risk
  have hG : Measurable (fun p : X × ℝ => ENNReal.ofReal (L p.1 p.2 (f p.1))) :=
    (L.measurable.comp
      (measurable_fst.prodMk (measurable_snd.prodMk (hf.comp measurable_fst)))).ennreal_ofReal
  rw [disint P hS.hY η hS.meas hS.h01 hS.hη _ hG]
  refine lintegral_congr fun x => ?_
  have h0 := (hS.h01 x).1
  have h1 : 0 ≤ 1 - η x := by linarith [(hS.h01 x).2]
  simp only [cond]
  rw [ENNReal.ofReal_add (mul_nonneg h0 (L.nonneg _ _ _)) (mul_nonneg h1 (L.nonneg _ _ _)),
    ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1]

theorem bayes_eq (L : Loss X) (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ}
    (hS : Setup P η) (m : X → ℝ) (hlow : ∀ x t, m x ≤ cond L η x t) (f₀ : X → ℝ)
    (hf₀ : Measurable f₀) (heq : ∀ x, cond L η x (f₀ x) = m x) :
    bayesRisk L P = ∫⁻ x, ENNReal.ofReal (m x) ∂(P.map Prod.fst) := by
  apply le_antisymm
  · calc bayesRisk L P ≤ risk L P f₀ := iInf₂_le f₀ hf₀
      _ = _ := by
        rw [risk_eq L P hS hf₀]
        exact lintegral_congr fun x => by rw [heq]
  · refine le_iInf₂ fun f hf => ?_
    rw [risk_eq L P hS hf]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hlow x _)

theorem cond_hinge (η : X → ℝ) (x : X) (t : ℝ) :
    cond hingeLoss η x t = hingeC (η x) t := by
  unfold cond hingeC
  show η x * max 0 (1 - 1 * t) + (1 - η x) * max 0 (1 - (-1) * t) = _
  simp

theorem cond_class (η : X → ℝ) (x : X) (t : ℝ) :
    cond classLoss η x t = classC (η x) t := by
  unfold cond classC
  show η x * (if 1 * sgn t ≤ 0 then 1 else 0) + (1 - η x) * (if -1 * sgn t ≤ 0 then 1 else 0) = _
  by_cases ht : t < 0
  · simp [sgn, ht]
  · simp [sgn, ht]

theorem measurable_bayesClassifier {η : X → ℝ} (hη : Measurable η) :
    Measurable (bayesClassifier η) :=
  measurable_sgn.comp ((measurable_const.mul hη).sub measurable_const)

theorem bayes_hinge (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ} (hS : Setup P η) :
    bayesRisk hingeLoss P =
      ∫⁻ x, ENNReal.ofReal (2 * min (η x) (1 - η x)) ∂(P.map Prod.fst) :=
  bayes_eq hingeLoss P hS (fun x => 2 * min (η x) (1 - η x))
    (fun x t => by
      rw [cond_hinge]
      exact hinge_lower (hS.h01 x).1 (hS.h01 x).2 t)
    (bayesClassifier η) (measurable_bayesClassifier hS.meas)
    (fun x => by
      rw [cond_hinge]
      exact hinge_at_bayes (hS.h01 x).1 (hS.h01 x).2)

theorem bayes_class (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ} (hS : Setup P η) :
    bayesRisk classLoss P =
      ∫⁻ x, ENNReal.ofReal (min (η x) (1 - η x)) ∂(P.map Prod.fst) :=
  bayes_eq classLoss P hS (fun x => min (η x) (1 - η x))
    (fun x t => by
      rw [cond_class]
      exact class_lower (hS.h01 x).1 (hS.h01 x).2 t)
    (bayesClassifier η) (measurable_bayesClassifier hS.meas)
    (fun x => by
      rw [cond_class]
      exact class_at_bayes (hS.h01 x).1 (hS.h01 x).2)

theorem min_nonneg' {η : ℝ} (h : η ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ min η (1 - η) :=
  le_min h.1 (by linarith [h.2])

theorem min_le_half {η : ℝ} : min η (1 - η) ≤ 1 / 2 := by
  rcases le_total η (1 - η) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem part1 (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ} (hS : Setup P η)
    {f : X → ℝ} (hf : Measurable f) (hf1 : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    risk hingeLoss P f - bayesRisk hingeLoss P =
      ∫⁻ x, ENNReal.ofReal (|f x - bayesClassifier η x| * |2 * η x - 1|) ∂(P.map Prod.fst) := by
  have : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [bayes_hinge P hS, risk_eq hingeLoss P hS hf]
  set B := ∫⁻ x, ENNReal.ofReal (2 * min (η x) (1 - η x)) ∂(P.map Prod.fst) with hB
  have hBtop : B ≠ ⊤ := by
    have hB1 : B ≤ 1 := by
      calc B ≤ ∫⁻ _x, 1 ∂(P.map Prod.fst) :=
            lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (by linarith [@min_le_half (η x)])
        _ = 1 := by simp
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hB1
  have hm : Measurable (fun x => ENNReal.ofReal (2 * min (η x) (1 - η x))) :=
    (measurable_const.mul (hS.meas.min (measurable_const.sub hS.meas))).ennreal_ofReal
  have key : ∫⁻ x, ENNReal.ofReal (cond hingeLoss η x (f x)) ∂(P.map Prod.fst) =
      B + ∫⁻ x, ENNReal.ofReal (|f x - bayesClassifier η x| * |2 * η x - 1|)
        ∂(P.map Prod.fst) := by
    rw [hB, ← lintegral_add_left hm]
    refine lintegral_congr fun x => ?_
    rw [cond_hinge, hinge_identity (hS.h01 x).1 (hS.h01 x).2 (hf1 x),
      ENNReal.ofReal_add (mul_nonneg two_pos.le (min_nonneg' (hS.h01 x)))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    rfl
  rw [key, ENNReal.add_sub_cancel_left hBtop]

theorem part2 (P : Measure (X × ℝ)) [IsProbabilityMeasure P] {η : X → ℝ} (hS : Setup P η)
    {f : X → ℝ} (hf : Measurable f) :
    risk classLoss P f - bayesRisk classLoss P ≤ risk hingeLoss P f - bayesRisk hingeLoss P := by
  have : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hbc := bayes_class P hS
  have hbh := bayes_hinge P hS
  set a := ∫⁻ x, ENNReal.ofReal (min (η x) (1 - η x)) ∂(P.map Prod.fst) with ha
  have hmeas : Measurable (fun x => ENNReal.ofReal (min (η x) (1 - η x))) :=
    (hS.meas.min (measurable_const.sub hS.meas)).ennreal_ofReal
  have hatop : a ≠ ⊤ := by
    have : a ≤ 1 := by
      calc a ≤ ∫⁻ _x, 1 ∂(P.map Prod.fst) :=
            lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (by linarith [@min_le_half (η x)])
        _ = 1 := by simp
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hb2 : bayesRisk hingeLoss P = a + a := by
    rw [hbh, ha, ← lintegral_add_left hmeas]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_add (min_nonneg' (hS.h01 x)) (min_nonneg' (hS.h01 x))]
    congr 1; ring
  have hAa : a ≤ risk classLoss P f := by
    rw [← hbc]; exact iInf₂_le f hf
  have hsum : risk classLoss P f + a ≤ risk hingeLoss P f := by
    rw [risk_eq classLoss P hS hf, risk_eq hingeLoss P hS hf, ha, ← lintegral_add_right _ hmeas]
    refine lintegral_mono fun x => ?_
    have hc0 : 0 ≤ cond classLoss η x (f x) := by
      rw [cond_class]
      exact (min_nonneg' (hS.h01 x)).trans (class_lower (hS.h01 x).1 (hS.h01 x).2 _)
    rw [← ENNReal.ofReal_add hc0 (min_nonneg' (hS.h01 x))]
    apply ENNReal.ofReal_le_ofReal
    rw [cond_class, cond_hinge]
    exact zhang_pointwise (hS.h01 x).1 (hS.h01 x).2 _
  rw [hbc, hb2]
  refine ENNReal.le_sub_of_add_le_right (ENNReal.add_ne_top.mpr ⟨hatop, hatop⟩) ?_
  calc risk classLoss P f - a + (a + a) = (risk classLoss P f - a + a) + a := by rw [add_assoc]
    _ = risk classLoss P f + a := by rw [tsub_add_cancel_of_le hAa]
    _ ≤ risk hingeLoss P f := hsum

end ZhangProof

open SupportVectorMachines.LossFunctions in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ)
    (hη_meas : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hη : ∀ A, MeasurableSet A →
      P (A ×ˢ ({1} : Set ℝ)) = ∫⁻ x in A, ENNReal.ofReal (η x) ∂(P.map Prod.fst)) :
    (∀ f : X → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) →
        risk hingeLoss P f - bayesRisk hingeLoss P =
          ∫⁻ x, ENNReal.ofReal (|f x - bayesClassifier η x| * |2 * η x - 1|)
            ∂(P.map Prod.fst)) ∧
      ∀ f : X → ℝ, Measurable f →
        risk classLoss P f - bayesRisk classLoss P ≤
          risk hingeLoss P f - bayesRisk hingeLoss P := by
  have hS : ZhangProof.Setup P η := ⟨hY, hη_meas, hη01, hη⟩
  exact ⟨fun f hf hf1 => ZhangProof.part1 P hS hf hf1, fun f hf => ZhangProof.part2 P hS hf⟩
