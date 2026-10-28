-- Prove2me | solution 1 for SoftRobust.Duality.inf_reparam
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:58:37.559725+00:00
-- url     : https://prove2.me/submissions/e31cf351-2c5e-4e89-969d-0ee4561c2660

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace Aux_SoftRobust_Duality_inf_reparam

lemma ereal_le_of_forall {x : EReal} {v : ℝ}
    (h : ∀ η : ℝ, 0 < η → x ≤ ((v + η : ℝ) : EReal)) : x ≤ (v : EReal) := by
  by_contra hlt
  push_neg at hlt
  have h1 := h 1 one_pos
  have hx1 : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
  have hx2 : x ≠ ⊥ := ne_bot_of_gt hlt
  rw [← EReal.coe_toReal hx1 hx2] at hlt h
  have hr : v < x.toReal := EReal.coe_lt_coe_iff.1 hlt
  have h2 := h ((x.toReal - v) / 2) (by linarith)
  have h3 : x.toReal ≤ v + (x.toReal - v) / 2 := EReal.coe_le_coe_iff.1 h2
  linarith

end Aux_SoftRobust_Duality_inf_reparam

open Aux_SoftRobust_Duality_inf_reparam in
open SoftRobust.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (M : Model Ω n m)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M.X) :
    (⨅ (ε : ℝ≥0) (_ : (ε : ℝ) ≤ δ) (Q : ProbabilityMeasure Ω) (_ : Q ∈ 𝒬 ε),
        (((∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + (ε : ℝ) : ℝ) : EReal)) =
      ⨅ (Q : ProbabilityMeasure Ω) (_ : penaltyOfFamily 𝒬 Q ≤ ENNReal.ofReal δ),
        ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal) := by
  set E : ProbabilityMeasure Ω → ℝ := fun Q => ∫ ω, M.payoff x ω ∂(Q : Measure Ω) with hE
  obtain ⟨C0, hC0⟩ := M.payoff_bounded x hx
  set C := max C0 0 with hCdef
  have hC : ∀ ω, |M.payoff x ω| ≤ C := fun ω => (hC0 ω).trans (le_max_left _ _)
  have hCnn : 0 ≤ C := le_max_right _ _
  have hpm : Measurable (M.payoff x) := M.payoff_measurable x hx
  have hint : ∀ μ : Measure Ω, IsFiniteMeasure μ → Integrable (M.payoff x) μ := by
    intro μ _
    exact Integrable.of_bound hpm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
  have hEb : ∀ Q : ProbabilityMeasure Ω, |E Q| ≤ C := by
    intro Q
    have := norm_integral_le_of_norm_le_const (μ := (Q : Measure Ω)) (f := M.payoff x) (C := C)
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact this
  have hmixE : ∀ (t : ℝ≥0) (ht : t ≤ 1) (Q1 Q2 : ProbabilityMeasure Ω),
      E (mix t ht Q1 Q2) = (t : ℝ) * E Q1 + (1 - (t : ℝ)) * E Q2 := by
    intro t ht Q1 Q2
    simp only [hE]
    rw [coe_mix, integral_add_measure
      ((hint _ inferInstance).smul_measure ENNReal.coe_ne_top)
      ((hint _ inferInstance).smul_measure ENNReal.coe_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.coe_toReal, ENNReal.coe_toReal,
      NNReal.coe_sub ht, NNReal.coe_one, smul_eq_mul, smul_eq_mul]
  apply le_antisymm
  · -- LHS ≤ RHS
    apply le_iInf₂
    intro Q hQ
    have hfin : penaltyOfFamily 𝒬 Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQ
    set a : ℝ≥0 := (penaltyOfFamily 𝒬 Q).toNNReal with hadef
    have haQ : penaltyOfFamily 𝒬 Q = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
    have haδ : (a : ℝ) ≤ δ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
      rw [ENNReal.toReal_ofReal hδ.le, haQ, ENNReal.coe_toReal] at this
      exact this
    have hRHS : ((E Q : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal) = ((E Q + a : ℝ) : EReal) := by
      rw [haQ, EReal.coe_nnreal_eq_coe_real, ← EReal.coe_add]
    show _ ≤ ((E Q : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal)
    rw [hRHS]
    apply ereal_le_of_forall
    intro η hη
    set K : ℝ := 2 * C / δ + 1 with hK
    have hKpos : 0 < K := by positivity
    set η' : ℝ≥0 := ⟨η / K, (div_pos hη hKpos).le⟩ with hη'
    have hη'r : (η' : ℝ) = η / K := rfl
    have hη'pos : (0 : ℝ) < η' := by rw [hη'r]; exact div_pos hη hKpos
    have hlt : penaltyOfFamily 𝒬 Q < ((a + η' : ℝ≥0) : ℝ≥0∞) := by
      rw [haQ, ENNReal.coe_lt_coe]
      exact lt_add_of_pos_right _ (by exact_mod_cast hη'pos)
    unfold penaltyOfFamily at hlt
    obtain ⟨ε₁, hlt2⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hQε₁, hε₁lt⟩ := iInf_lt_iff.1 hlt2
    have hε₁ : (ε₁ : ℝ) < a + η' := by exact_mod_cast ENNReal.coe_lt_coe.1 hε₁lt
    have hε₁a : (a : ℝ) ≤ ε₁ := by
      have : penaltyOfFamily 𝒬 Q ≤ (ε₁ : ℝ≥0∞) := iInf₂_le ε₁ hQε₁
      rw [haQ, ENNReal.coe_le_coe] at this
      exact_mod_cast this
    have hη'η : (η' : ℝ) * K = η := by
      rw [hη'r]; field_simp
    rcases le_or_gt (ε₁ : ℝ) δ with hcase | hcase
    · calc (⨅ (ε : ℝ≥0) (_ : (ε : ℝ) ≤ δ) (Q : ProbabilityMeasure Ω) (_ : Q ∈ 𝒬 ε),
            (((∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + (ε : ℝ) : ℝ) : EReal))
          ≤ ((E Q + ε₁ : ℝ) : EReal) :=
            (iInf₂_le ε₁ hcase).trans (iInf₂_le Q hQε₁)
        _ ≤ ((E Q + a + η : ℝ) : EReal) := by
            apply EReal.coe_le_coe_iff.2
            have : (η' : ℝ) ≤ η := by
              rw [← hη'η]
              have : (1 : ℝ) ≤ K := by
                rw [hK]; have : 0 ≤ 2 * C / δ := by positivity
                linarith
              nlinarith
            linarith
    · obtain ⟨Q0, hQ0⟩ := h𝒬.zero_nonempty
      have hε₁pos : (0 : ℝ) < ε₁ := lt_trans hδ hcase
      set t : ℝ≥0 := ⟨δ / ε₁, by positivity⟩ with htdef
      have htr : (t : ℝ) = δ / ε₁ := rfl
      have ht1 : t ≤ 1 := by
        rw [← NNReal.coe_le_coe, htr, NNReal.coe_one, div_le_one hε₁pos]
        exact hcase.le
      have hmem := h𝒬.convex ε₁ 0 Q Q0 t ht1 hQε₁ hQ0
      rw [mul_zero, add_zero] at hmem
      have htε : ((t * ε₁ : ℝ≥0) : ℝ) = δ := by
        rw [NNReal.coe_mul, htr]; field_simp
      have hEmix := hmixE t ht1 Q Q0
      have hb1 := hEb Q
      have hb2 := hEb Q0
      calc (⨅ (ε : ℝ≥0) (_ : (ε : ℝ) ≤ δ) (Q : ProbabilityMeasure Ω) (_ : Q ∈ 𝒬 ε),
            (((∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + (ε : ℝ) : ℝ) : EReal))
          ≤ ((E (mix t ht1 Q Q0) + ((t * ε₁ : ℝ≥0) : ℝ) : ℝ) : EReal) :=
            (iInf₂_le (t * ε₁) htε.le).trans (iInf₂_le (mix t ht1 Q Q0) hmem)
        _ ≤ ((E Q + a + η : ℝ) : EReal) := by
            apply EReal.coe_le_coe_iff.2
            rw [hEmix, htε, htr]
            have hu0 : 0 ≤ 1 - δ / ε₁ := by
              rw [sub_nonneg, div_le_one hε₁pos]; exact hcase.le
            have hu : 1 - δ / ε₁ ≤ (ε₁ - δ) / δ := by
              rw [show 1 - δ / ε₁ = (ε₁ - δ) / ε₁ by field_simp]
              exact div_le_div_of_nonneg_left (by linarith) hδ hcase.le
            have hdE : E Q0 - E Q ≤ 2 * C := by
              have := le_abs_self (E Q0); have := neg_abs_le (E Q); linarith
            have f1 : (1 - δ / ε₁) * (E Q0 - E Q) ≤ 2 * C / δ * (ε₁ - δ) := by
              calc (1 - δ / ε₁) * (E Q0 - E Q) ≤ (1 - δ / ε₁) * (2 * C) :=
                    mul_le_mul_of_nonneg_left hdE hu0
                _ ≤ (ε₁ - δ) / δ * (2 * C) := mul_le_mul_of_nonneg_right hu (by positivity)
                _ = 2 * C / δ * (ε₁ - δ) := by ring
            have f2 : 2 * C / δ * (ε₁ - δ) ≤ 2 * C / δ * (ε₁ - a) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have f3 : K * (ε₁ - a) ≤ K * η' := mul_le_mul_of_nonneg_left (by linarith) hKpos.le
            have eK : K * (ε₁ - a) = 2 * C / δ * (ε₁ - a) + (ε₁ - a) := by rw [hK]; ring
            have eid : δ / ε₁ * E Q + (1 - δ / ε₁) * E Q0 =
                E Q + (1 - δ / ε₁) * (E Q0 - E Q) := by ring
            have hKη : K * η' = η := by rw [mul_comm]; exact hη'η
            linarith
  · -- RHS ≤ LHS
    apply le_iInf
    intro ε
    apply le_iInf
    intro hεδ
    apply le_iInf
    intro Q
    apply le_iInf
    intro hQ
    have hαε : penaltyOfFamily 𝒬 Q ≤ (ε : ℝ≥0∞) := iInf₂_le ε hQ
    have hαδ : penaltyOfFamily 𝒬 Q ≤ ENNReal.ofReal δ := by
      refine hαε.trans ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hεδ
    refine (iInf₂_le Q hαδ).trans ?_
    rw [EReal.coe_add]
    have : (penaltyOfFamily 𝒬 Q : EReal) ≤ ((ε : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 hαε
    rw [EReal.coe_nnreal_eq_coe_real] at this
    exact add_le_add le_rfl this
