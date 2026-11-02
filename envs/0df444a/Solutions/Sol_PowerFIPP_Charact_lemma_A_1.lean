-- Prove2me | solution 1 for PowerFIPP.Charact.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:18:06.428925+00:00
-- url     : https://prove2.me/submissions/b767d5cc-538e-445d-aa4e-306dd5b82264

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

open PowerFIPP.Charact

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ζ : ℝ≥0 → Ω → ℝ)
    (hζ : IsStronglyProgressive ℱ ζ) :
    ClassDL Q ℱ (fun t ω => ‖ζ t ω‖ₑ) ↔
      ∀ T : ℝ≥0, 0 < T →
        (⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ T τ),
            ∫⁻ ω, ‖stoppedValue ζ τ ω‖ₑ ∂Q) < ∞ ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set Ω, MeasurableSet[ℱ T] A →
          Q A ≤ ENNReal.ofReal δ →
          (⨆ (τ : Ω → WithTop ℝ≥0) (hτ : IsBoundedStop ℱ T τ)
              (_ : MeasurableSet[hτ.1.measurableSpace] A),
              ∫⁻ ω in A, ‖stoppedValue ζ τ ω‖ₑ ∂Q) ≤ ENNReal.ofReal ε := by
  -- the stopped value of `‖ζ‖ₑ` is the norm of the stopped value of `ζ`
  have hcomp : ∀ τ : Ω → WithTop ℝ≥0,
      stoppedValue (fun t ω => ‖ζ t ω‖ₑ) τ = fun ω => ‖stoppedValue ζ τ ω‖ₑ := fun τ => rfl
  -- measurability of the stopped value with respect to `𝓕_τ` and to the ambient σ-algebra
  have hmτ : ∀ (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (hτ : IsBoundedStop ℱ T τ),
      Measurable[hτ.1.measurableSpace] (fun ω => ‖stoppedValue ζ τ ω‖ₑ) :=
    fun T τ hτ => measurable_enorm.comp (measurable_stoppedValue hζ hτ.1)
  have hm : ∀ (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (hτ : IsBoundedStop ℱ T τ),
      Measurable (fun ω => ‖stoppedValue ζ τ ω‖ₑ) :=
    fun T τ hτ => (hmτ T τ hτ).mono (hτ.1.measurableSpace_le_of_le hτ.2) le_rfl
  -- basic splitting bound: on a measurable set `A`, `∫_A g ≤ K Q(A) + ∫ g 1_{g > K}`
  have hsplit : ∀ (g : Ω → ℝ≥0∞) (K : ℝ≥0) (A : Set Ω), MeasurableSet A →
      ∫⁻ ω in A, g ω ∂Q ≤ (K : ℝ≥0∞) * Q A +
        ∫⁻ ω, {ω | (K : ℝ≥0∞) < g ω}.indicator g ω ∂Q := by
    intro g K A hA
    calc ∫⁻ ω in A, g ω ∂Q
        ≤ ∫⁻ ω in A, ((K : ℝ≥0∞) + {ω | (K : ℝ≥0∞) < g ω}.indicator g ω) ∂Q := by
          refine lintegral_mono fun ω => ?_
          by_cases h : (K : ℝ≥0∞) < g ω
          · simp [Set.indicator_of_mem (show ω ∈ {ω | (K : ℝ≥0∞) < g ω} from h)]
          · rw [not_lt] at h
            exact h.trans le_self_add
      _ = (K : ℝ≥0∞) * Q A + ∫⁻ ω in A, {ω | (K : ℝ≥0∞) < g ω}.indicator g ω ∂Q := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm]
      _ ≤ (K : ℝ≥0∞) * Q A + ∫⁻ ω, {ω | (K : ℝ≥0∞) < g ω}.indicator g ω ∂Q := by
          exact add_le_add le_rfl (setLIntegral_le_lintegral _ _)
  constructor
  · -- class (DL) ⟹ (i) and (ii)
    intro h T _
    have hT := h T
    rw [ENNReal.tendsto_nhds_zero] at hT
    refine ⟨?_, ?_⟩
    · obtain ⟨K, hK⟩ := (hT 1 one_pos).exists_forall_of_atTop
      have hK' := hK K le_rfl
      refine lt_of_le_of_lt (b := (K : ℝ≥0∞) + 1) ?_ (by simp)
      refine iSup₂_le fun τ hτ => ?_
      have h1 := hsplit (fun ω => ‖stoppedValue ζ τ ω‖ₑ) K Set.univ MeasurableSet.univ
      rw [Measure.restrict_univ, measure_univ, mul_one] at h1
      refine h1.trans (add_le_add le_rfl ?_)
      refine le_trans ?_ hK'
      rw [← hcomp τ]
      exact le_iSup₂ (f := fun (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ T τ) =>
        ∫⁻ ω, {ω | (K : ℝ≥0∞) < stoppedValue (fun t ω => ‖ζ t ω‖ₑ) τ ω}.indicator
          (stoppedValue (fun t ω => ‖ζ t ω‖ₑ) τ) ω ∂Q) τ hτ
    · intro ε hε
      have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by
        rw [ENNReal.ofReal_pos]; linarith
      obtain ⟨K0, hK0⟩ := (hT _ hε2).exists_forall_of_atTop
      set K : ℝ≥0 := max K0 1 with hKdef
      have hKpos : (0 : ℝ) < (K : ℝ) := by
        have : (1 : ℝ≥0) ≤ K := le_max_right _ _
        exact_mod_cast lt_of_lt_of_le one_pos this
      have hK := hK0 K (le_max_left _ _)
      refine ⟨ε / (2 * K), by positivity, fun A hA hQA => ?_⟩
      refine iSup₂_le fun τ hτ => iSup_le fun _ => ?_
      have hAm : MeasurableSet A := ℱ.le T A hA
      have h1 := hsplit (fun ω => ‖stoppedValue ζ τ ω‖ₑ) K A hAm
      refine h1.trans ?_
      have htail : ∫⁻ ω, {ω | (K : ℝ≥0∞) < ‖stoppedValue ζ τ ω‖ₑ}.indicator
          (fun ω => ‖stoppedValue ζ τ ω‖ₑ) ω ∂Q ≤ ENNReal.ofReal (ε / 2) := by
        refine le_trans ?_ hK
        rw [← hcomp τ]
        exact le_iSup₂ (f := fun (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ T τ) =>
          ∫⁻ ω, {ω | (K : ℝ≥0∞) < stoppedValue (fun t ω => ‖ζ t ω‖ₑ) τ ω}.indicator
            (stoppedValue (fun t ω => ‖ζ t ω‖ₑ) τ) ω ∂Q) τ hτ
      have hKQ : (K : ℝ≥0∞) * Q A ≤ ENNReal.ofReal (ε / 2) := by
        calc (K : ℝ≥0∞) * Q A ≤ (K : ℝ≥0∞) * ENNReal.ofReal (ε / (2 * K)) := by gcongr
          _ = ENNReal.ofReal ((K : ℝ) * (ε / (2 * K))) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
          _ = ENNReal.ofReal (ε / 2) := by
              congr 1; field_simp
      calc (K : ℝ≥0∞) * Q A + ∫⁻ ω, {ω | (K : ℝ≥0∞) < ‖stoppedValue ζ τ ω‖ₑ}.indicator
            (fun ω => ‖stoppedValue ζ τ ω‖ₑ) ω ∂Q
          ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hKQ htail
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · -- (i) and (ii) ⟹ class (DL)
    intro h T
    obtain ⟨hC, hδ⟩ := h (T + 1) (by positivity)
    set C := ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ (T + 1) τ),
      ∫⁻ ω, ‖stoppedValue ζ τ ω‖ₑ ∂Q with hCdef
    have hCne : C ≠ ⊤ := hC.ne
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact Eventually.of_forall fun _ => hεtop ▸ le_top
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    obtain ⟨δ, hδpos, hδA⟩ := hδ ε.toReal hε'
    rw [Filter.eventually_atTop]
    refine ⟨Real.toNNReal (C.toReal / δ) + 1, fun K hK => ?_⟩
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (1 : ℝ≥0) ≤ K := le_trans le_add_self hK
      exact_mod_cast lt_of_lt_of_le one_pos this
    have hKge : C.toReal ≤ (K : ℝ) * δ := by
      have h1 : C.toReal / δ ≤ (K : ℝ) := by
        have : Real.toNNReal (C.toReal / δ) ≤ K := le_trans le_self_add hK
        have h2 := (Real.toNNReal_le_iff_le_coe).1 this
        exact h2
      rwa [div_le_iff₀ hδpos] at h1
    refine iSup₂_le fun τ hτ => ?_
    rw [hcomp τ]
    have hτ' : IsBoundedStop ℱ (T + 1) τ :=
      ⟨hτ.1, fun ω => (hτ.2 ω).trans (by exact_mod_cast le_self_add)⟩
    set g := fun ω => ‖stoppedValue ζ τ ω‖ₑ with hgdef
    set A := {ω | (K : ℝ≥0∞) < g ω} with hAdef
    have hAτ : MeasurableSet[hτ'.1.measurableSpace] A :=
      measurableSet_lt measurable_const (hmτ _ τ hτ')
    have hAT : MeasurableSet[ℱ (T + 1)] A :=
      hτ'.1.measurableSpace_le_of_le_const hτ'.2 A hAτ
    have hAm : MeasurableSet A := ℱ.le _ A hAT
    have hgint : ∫⁻ ω, g ω ∂Q ≤ C :=
      le_iSup₂ (f := fun (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ (T + 1) τ) =>
        ∫⁻ ω, ‖stoppedValue ζ τ ω‖ₑ ∂Q) τ hτ'
    -- Markov's inequality: `K Q(A) ≤ ∫ g ≤ C ≤ K δ`
    have hQA : Q A ≤ ENNReal.ofReal δ := by
      have hmk : (K : ℝ≥0∞) * Q {ω | (K : ℝ≥0∞) ≤ g ω} ≤ ∫⁻ ω, g ω ∂Q :=
        mul_meas_ge_le_lintegral₀ (hm _ τ hτ').aemeasurable _
      have hsub : Q A ≤ Q {ω | (K : ℝ≥0∞) ≤ g ω} :=
        measure_mono fun ω (hω : (K : ℝ≥0∞) < g ω) => (le_of_lt hω : (K : ℝ≥0∞) ≤ g ω)
      have hKC : (K : ℝ≥0∞) * Q A ≤ (K : ℝ≥0∞) * ENNReal.ofReal δ := by
        calc (K : ℝ≥0∞) * Q A ≤ (K : ℝ≥0∞) * Q {ω | (K : ℝ≥0∞) ≤ g ω} := by gcongr
          _ ≤ C := hmk.trans hgint
          _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hCne).symm
          _ ≤ ENNReal.ofReal ((K : ℝ) * δ) := ENNReal.ofReal_le_ofReal hKge
          _ = (K : ℝ≥0∞) * ENNReal.ofReal δ := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
      have hK0 : (K : ℝ≥0∞) ≠ 0 := by
        have : (K : ℝ) ≠ 0 := hKpos.ne'
        exact_mod_cast this
      exact (ENNReal.mul_le_mul_iff_right hK0 ENNReal.coe_ne_top).1 hKC
    have hfin := hδA A hAT hQA
    calc ∫⁻ ω, A.indicator g ω ∂Q = ∫⁻ ω in A, g ω ∂Q := lintegral_indicator hAm _
      _ ≤ ⨆ (τ : Ω → WithTop ℝ≥0) (hτ : IsBoundedStop ℱ (T + 1) τ)
              (_ : MeasurableSet[hτ.1.measurableSpace] A),
              ∫⁻ ω in A, ‖stoppedValue ζ τ ω‖ₑ ∂Q :=
          le_iSup_of_le τ (le_iSup_of_le hτ' (le_iSup_of_le hAτ le_rfl))
      _ ≤ ENNReal.ofReal ε.toReal := hfin
      _ = ε := ENNReal.ofReal_toReal hεtop
