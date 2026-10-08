-- Prove2me | solution 1 for PalmQueueing.Ergodic.extremal_discrete
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:08:59.341596+00:00
-- url     : https://prove2.me/submissions/523df575-b2db-4f15-962b-d11ba70bd872

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow



namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The level sets of the Radon–Nikodým density of an invariant `Q ≪ P` are a.e. invariant. -/
lemma rn_level_ae_invariant (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (T : Ω → Ω) (hT : Measurable T) (hP : Measure.map T P = P) (hQ : Measure.map T Q = Q)
    (hQP : Q ≪ P) (c : ℝ) :
    P ({ω | c < (Q.rnDeriv P ω).toReal} \ T ⁻¹' {ω | c < (Q.rnDeriv P ω).toReal}) = 0 ∧
    P (T ⁻¹' {ω | c < (Q.rnDeriv P ω).toReal} \ {ω | c < (Q.rnDeriv P ω).toReal}) = 0 := by
  set f : Ω → ℝ := fun ω => (Q.rnDeriv P ω).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hfi : Integrable f P := Measure.integrable_toReal_rnDeriv
  set A : Set Ω := {ω | c < f ω} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hfm
  set B : Set Ω := T ⁻¹' A with hB
  have hBm : MeasurableSet B := hT hAm
  have hQAB : Q.real B = Q.real A := by
    simp only [measureReal_def, hB]
    rw [← Measure.map_apply hT hAm, hQ]
  have hPAB : P.real B = P.real A := by
    simp only [measureReal_def, hB]
    rw [← Measure.map_apply hT hAm, hP]
  have hIA : ∫ ω in A, f ω ∂P = Q.real A := Measure.setIntegral_toReal_rnDeriv hQP A
  have hIB : ∫ ω in B, f ω ∂P = Q.real B := Measure.setIntegral_toReal_rnDeriv hQP B
  have hsplitA : ∫ ω in A, f ω ∂P = ∫ ω in A \ B, f ω ∂P + ∫ ω in A ∩ B, f ω ∂P := by
    rw [← setIntegral_union Set.disjoint_sdiff_inter (hAm.inter hBm) hfi.integrableOn
      hfi.integrableOn, Set.diff_union_inter]
  have hsplitB : ∫ ω in B, f ω ∂P = ∫ ω in B \ A, f ω ∂P + ∫ ω in A ∩ B, f ω ∂P := by
    rw [Set.inter_comm, ← setIntegral_union Set.disjoint_sdiff_inter (hBm.inter hAm)
      hfi.integrableOn hfi.integrableOn, Set.diff_union_inter]
  have hdiffeq : ∫ ω in A \ B, f ω ∂P = ∫ ω in B \ A, f ω ∂P := by
    linarith
  have hmeasAB : P.real (A \ B) = P.real (B \ A) := by
    have e1 : A \ B = A \ (A ∩ B) := Set.diff_self_inter.symm
    have e2 : B \ A = B \ (A ∩ B) := by rw [Set.inter_comm]; exact Set.diff_self_inter.symm
    rw [e1, e2, measureReal_sdiff Set.inter_subset_left (hAm.inter hBm),
      measureReal_sdiff Set.inter_subset_right (hAm.inter hBm), hPAB]
  -- lower bound on A \ B, upper bound on B \ A
  have hlow : c * P.real (A \ B) ≤ ∫ ω in A \ B, f ω ∂P :=
    setIntegral_ge_of_const_le_real (hAm.diff hBm) (measure_ne_top _ _)
      (fun x hx => le_of_lt hx.1) hfi.integrableOn
  have hup : ∫ ω in B \ A, f ω ∂P ≤ c * P.real (B \ A) := by
    have := setIntegral_mono_on (f := f) (g := fun _ => c) hfi.integrableOn
      (integrable_const c).integrableOn (hBm.diff hAm) (fun x hx => by
        have : ¬ c < f x := hx.2
        exact not_lt.1 this)
    simpa [setIntegral_const, mul_comm] using this
  have hzero : ∫ ω in A \ B, (f ω - c) ∂P = 0 := by
    rw [integral_sub hfi.integrableOn (integrable_const c).integrableOn, setIntegral_const]
    simp only [smul_eq_mul]
    rw [hmeasAB] at hlow ⊢
    rw [hdiffeq]
    linarith
  have hnn : 0 ≤ᵐ[P.restrict (A \ B)] fun ω => f ω - c := by
    rw [Filter.EventuallyLE, ae_restrict_iff' (hAm.diff hBm)]
    exact ae_of_all _ fun x hx => by
      have := hx.1; simp only [hA, Set.mem_setOf_eq] at this; simp only [Pi.zero_apply]; linarith
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hnn
    (hfi.integrableOn.sub (integrable_const c).integrableOn)).1 hzero
  rw [Filter.EventuallyEq, ae_restrict_iff' (hAm.diff hBm)] at hae
  have h1 : P (A \ B) = 0 := by
    have : ∀ᵐ ω ∂P, ω ∉ A \ B := by
      filter_upwards [hae] with ω hω
      intro hmem
      have h0 := hω hmem
      have := hmem.1
      simp only [hA, Set.mem_setOf_eq] at this
      simp only [Pi.zero_apply] at h0
      linarith
    have := ae_iff.1 this
    simp only [not_not] at this
    exact this
  refine ⟨h1, ?_⟩
  have : P.real (B \ A) = 0 := by
    rw [← hmeasAB, measureReal_def, h1]; simp
  exact (measureReal_eq_zero_iff).1 this


/-- If every level set of the density is null or co-null, then `Q = P`. -/
lemma eq_of_rn_levels (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (hlev : ∀ c : ℝ, P {ω | c < (Q.rnDeriv P ω).toReal} = 0 ∨
      P {ω | c < (Q.rnDeriv P ω).toReal}ᶜ = 0) :
    Q = P := by
  set f : Ω → ℝ := fun ω => (Q.rnDeriv P ω).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hfi : Integrable f P := Measure.integrable_toReal_rnDeriv
  have hint : ∫ ω, f ω ∂P = 1 := by
    rw [Measure.integral_toReal_rnDeriv hQP]; simp
  have hnn : ∀ ω, 0 ≤ f ω := fun ω => ENNReal.toReal_nonneg
  -- f ≤ 1 a.e.
  have hle : ∀ᵐ ω ∂P, f ω ≤ 1 := by
    rcases hlev 1 with h | h
    · rw [ae_iff]; simpa using h
    · exfalso
      have hgt : ∀ᵐ ω ∂P, 1 < f ω := by
        rw [ae_iff, ← Set.compl_setOf]; exact h
      have h0 : ∫ ω, (f ω - 1) ∂P = 0 := by
        rw [integral_sub hfi (integrable_const _), hint]; simp
      have hnn' : 0 ≤ᵐ[P] fun ω => f ω - 1 := by
        filter_upwards [hgt] with ω hω; simp only [Pi.zero_apply]; linarith
      have := (integral_eq_zero_iff_of_nonneg_ae hnn' (hfi.sub (integrable_const _))).1 h0
      have hbad : ∀ᵐ ω ∂P, False := by
        filter_upwards [hgt, this] with ω h1 h2
        simp only [Pi.zero_apply] at h2; linarith
      rw [ae_iff] at hbad
      simp at hbad
  -- f ≥ 1 a.e.
  have hge : ∀ᵐ ω ∂P, 1 ≤ f ω := by
    have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, 1 - 1 / ((n : ℝ) + 1) < f ω := by
      intro n
      rcases hlev (1 - 1 / ((n : ℝ) + 1)) with h | h
      · exfalso
        have hle' : ∀ᵐ ω ∂P, f ω ≤ 1 - 1 / ((n : ℝ) + 1) := by
          rw [ae_iff]; simpa using h
        have := integral_mono_ae hfi (integrable_const _) hle'
        rw [hint] at this
        simp only [integral_const, smul_eq_mul] at this
        rw [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at this
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · rw [ae_iff, ← Set.compl_setOf]; exact h
    have hall := ae_all_iff.2 hn
    filter_upwards [hall] with ω hω
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hcon)
    have := hω n
    linarith
  have hone : ∀ᵐ ω ∂P, f ω = 1 := by
    filter_upwards [hle, hge] with ω h1 h2; linarith
  ext s hs
  have h1 := Measure.setIntegral_toReal_rnDeriv hQP s
  have h2 : ∫ ω in s, f ω ∂P = ∫ ω in s, (1 : ℝ) ∂P :=
    setIntegral_congr_ae hs (by filter_upwards [hone] with ω hω _; exact hω)
  rw [setIntegral_const, smul_eq_mul, mul_one] at h2
  have h3 : Q.real s = P.real s := by rw [← h1]; exact h2
  simp only [measureReal_def] at h3
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

/-- From a non-trivial invariant set, build a non-trivial decomposition. -/
lemma decomposition_of_set (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s) (h0 : P s ≠ 0) (h1 : P sᶜ ≠ 0) :
    ∃ (a₁ a₂ : ℝ) (Q₁ Q₂ : Measure Ω),
      IsProbabilityMeasure Q₁ ∧ IsProbabilityMeasure Q₂ ∧
      0 < a₁ ∧ 0 < a₂ ∧ a₁ + a₂ = 1 ∧ Q₁ ≠ Q₂ ∧
      (∀ T : Ω → Ω, Measurable T → Measure.map T P = P → T ⁻¹' s = s →
        Measure.map T Q₁ = Q₁ ∧ Measure.map T Q₂ = Q₂) ∧
      P = ENNReal.ofReal a₁ • Q₁ + ENNReal.ofReal a₂ • Q₂ := by
  set Q₁ : Measure Ω := (P s)⁻¹ • P.restrict s with hQ₁
  set Q₂ : Measure Ω := (P sᶜ)⁻¹ • P.restrict sᶜ with hQ₂
  have hs' : MeasurableSet sᶜ := hs.compl
  have hfin1 : P s ≠ ⊤ := measure_ne_top _ _
  have hfin2 : P sᶜ ≠ ⊤ := measure_ne_top _ _
  have hp1 : IsProbabilityMeasure Q₁ := ⟨by
    simp only [hQ₁, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 hfin1⟩
  have hp2 : IsProbabilityMeasure Q₂ := ⟨by
    simp only [hQ₂, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h1 hfin2⟩
  refine ⟨(P s).toReal, (P sᶜ).toReal, Q₁, Q₂, hp1, hp2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.toReal_pos h0 hfin1
  · exact ENNReal.toReal_pos h1 hfin2
  · rw [← ENNReal.toReal_add hfin1 hfin2, measure_add_measure_compl hs]; simp
  · intro heq
    have e1 : Q₁ s = 1 := by
      simp only [hQ₁, Measure.smul_apply, Measure.restrict_apply hs, Set.inter_self, smul_eq_mul]
      exact ENNReal.inv_mul_cancel h0 hfin1
    have e2 : Q₂ s = 0 := by
      simp only [hQ₂, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
      simp
    rw [heq, e2] at e1
    exact zero_ne_one e1
  · intro T hT hP hTs
    constructor
    · simp only [hQ₁]
      rw [Measure.map_smul, ← hTs, ← Measure.restrict_map hT hs, hP, hTs]
    · simp only [hQ₂]
      have hTs' : T ⁻¹' sᶜ = sᶜ := by rw [Set.preimage_compl, hTs]
      rw [Measure.map_smul, ← hTs', ← Measure.restrict_map hT hs', hP, hTs']
  · simp only [hQ₁, hQ₂, ENNReal.ofReal_toReal hfin1, ENNReal.ofReal_toReal hfin2, smul_smul,
      ENNReal.mul_inv_cancel h0 hfin1, ENNReal.mul_inv_cancel h1 hfin2, one_smul]
    exact (Measure.restrict_add_restrict_compl hs).symm

/-- Forward direction: an invariant `Q ≪ P` with `P` ergodic equals `P`. -/
lemma eq_of_ergodic_absolutelyContinuous (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (θ : Ω → Ω) (herg : Ergodic θ P) (hQ : Measure.map θ Q = Q)
    (hQP : Q ≪ P) : Q = P := by
  have hθ : Measurable θ := herg.toMeasurePreserving.measurable
  have hP : Measure.map θ P = P := herg.toMeasurePreserving.map_eq
  apply eq_of_rn_levels P Q hQP
  intro c
  obtain ⟨-, h2⟩ := rn_level_ae_invariant P Q θ hθ hP hQ hQP c
  set A := {ω | c < (Q.rnDeriv P ω).toReal} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hle : θ ⁻¹' A ≤ᵐ[P] A := ae_le_set.2 h2
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hAm.nullMeasurableSet hle with h | h
  · left; exact ae_eq_empty.1 h
  · right; exact ae_eq_univ.1 h

theorem extremal_discrete_core (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ)
    (hinv : Measure.map θ P0 = P0) :
    Ergodic θ P0 ↔ ¬ HasInvariantDecomposition θ P0 := by
  constructor
  · intro herg hdec
    obtain ⟨a₁, a₂, Q₁, Q₂, hp1, hp2, ha1, ha2, hsum, hne, hi1, hi2, hP⟩ := hdec
    have hac : ∀ (Q : Measure Ω) (Q' : Measure Ω) (a a' : ℝ), 0 < a →
        P0 = ENNReal.ofReal a • Q + ENNReal.ofReal a' • Q' → Q ≪ P0 := by
      intro Q Q' a a' ha hP s hs
      rw [hP] at hs
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hs
      rcases add_eq_zero.1 hs with ⟨h, -⟩
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (ENNReal.ofReal_pos.2 ha).ne'
      · exact h
    have e1 : Q₁ = P0 := eq_of_ergodic_absolutelyContinuous P0 Q₁ θ herg hi1 (hac Q₁ Q₂ a₁ a₂ ha1 hP)
    have e2 : Q₂ = P0 := eq_of_ergodic_absolutelyContinuous P0 Q₂ θ herg hi2
      (hac Q₂ Q₁ a₂ a₁ ha2 (by rw [hP, add_comm]))
    exact hne (e1.trans e2.symm)
  · intro hnd
    refine ⟨⟨hθ, hinv⟩, ⟨fun s hs hinvs => ?_⟩⟩
    by_contra hcon
    rw [Filter.eventuallyConst_set', not_or, ae_eq_empty, ae_eq_univ] at hcon
    obtain ⟨a₁, a₂, Q₁, Q₂, hp1, hp2, ha1, ha2, hsum, hne, hT, hP⟩ :=
      decomposition_of_set P0 s hs hcon.1 hcon.2
    obtain ⟨hi1, hi2⟩ := hT θ hθ hinv hinvs
    exact hnd ⟨a₁, a₂, Q₁, Q₂, hp1, hp2, ha1, ha2, hsum, hne, hi1, hi2, hP⟩

end PalmQueueing.Ergodic

open PalmQueueing.Ergodic
open MeasureTheory
open PalmQueueing.Palm
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (hinv : Measure.map θ P0 = P0) :
    Ergodic θ P0 ↔ ¬ HasInvariantDecomposition θ P0 := by
  exact extremal_discrete_core P0 θ hθ hbij hinv
