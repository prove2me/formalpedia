-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T10:00:29.276782+00:00
-- url     : https://prove2.me/submissions/9cf2394a-baf2-4158-9a1a-9cceb54f2389

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SSLLem5Aux
open SeqSocialLearning.Adequate

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [StandardBorelSpace Ω]
  [Nonempty Ω]

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F] :
    IsProbabilityMeasure (signalLaw μ F) := by
  unfold signalLaw; infer_instance

/-- Disintegration through the posterior. -/
lemma disint (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    {B : Set Ω} (hB : MeasurableSet B) {T : Set S} (hT : MeasurableSet T) :
    ∫⁻ ω in B, F ω T ∂μ = ∫⁻ s in T, (F†μ) s B ∂(F ∘ₘ μ) := by
  rw [← Measure.compProd_apply_prod hB hT, ← Measure.compProd_apply_prod hT hB,
    compProd_posterior_eq_map_swap, Measure.map_apply measurable_swap (hT.prod hB),
    Set.preimage_swap_prod]

lemma post_compl (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    {B : Set Ω} (hB : MeasurableSet B) (s : S) :
    privPost μ F Bᶜ s = 1 - privPost μ F B s := by
  unfold privPost
  rw [prob_compl_eq_one_sub hB, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp

lemma measurable_privPost (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S)
    [IsMarkovKernel F] {B : Set Ω} (hB : MeasurableSet B) : Measurable (privPost μ F B) :=
  (Kernel.measurable_coe _ hB).ennreal_toReal

lemma high (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hTU : TotallyUnbounded μ F)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ᵐ ω ∂μ, ν.rnDeriv μ ω ≤ ENNReal.ofReal C)
    {E : Set Ω} (hE : MeasurableSet E) (hE0 : 0 < ν E) (hE1 : ν E < 1) {ε : ℝ} (hε : 0 < ε) :
    0 < signalLaw ν F {s | 1 - ε < privPost ν F E s} := by
  set h := ν.rnDeriv μ with h_def
  have hh : Measurable h := Measure.measurable_rnDeriv _ _
  have hνeq : μ.withDensity h = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
  have hνint : ∀ {B : Set Ω}, MeasurableSet B → ∀ {T : Set S}, MeasurableSet T →
      ∫⁻ ω in B, F ω T ∂ν = ∫⁻ ω in B, h ω * F ω T ∂μ := by
    intro B hB T hT
    rw [← hνeq, setLIntegral_withDensity_eq_setLIntegral_mul _ hh (Kernel.measurable_coe F hT) hB]
    rfl
  -- a level `c` such that `G = E ∩ {c < h}` has positive prior probability
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < μ (E ∩ {ω | (n : ℝ≥0∞)⁻¹ < h ω}) := by
    by_contra hcon
    push Not at hcon
    have hsub : E ∩ {ω | 0 < h ω} ⊆ ⋃ n : ℕ, E ∩ {ω | (n : ℝ≥0∞)⁻¹ < h ω} := by
      rintro ω ⟨hω, hpos⟩
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
      exact Set.mem_iUnion.2 ⟨n, hω, hn⟩
    have h0 : μ (E ∩ {ω | 0 < h ω}) = 0 :=
      measure_mono_null hsub (measure_iUnion_null fun n => le_zero_iff.1 (hcon n))
    have : ν E = 0 := by
      rw [← hνeq, withDensity_apply _ hE]
      have hae : ∀ᵐ ω ∂μ.restrict E, h ω = 0 := by
        rw [ae_restrict_iff' hE]
        rw [ae_iff]
        refine measure_mono_null (fun ω hω => ?_) h0
        simp only [Set.mem_ofPred_eq, Classical.not_imp] at hω
        exact ⟨hω.1, pos_iff_ne_zero.2 hω.2⟩
      rw [lintegral_congr_ae hae, lintegral_zero]
    exact hE0.ne' this
  set c : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹ with hc_def
  set G := E ∩ {ω | c < h ω} with hG_def
  have hGm : MeasurableSet G := hE.inter (measurableSet_lt measurable_const hh)
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [c, G] at hn
  have hc0 : c ≠ 0 := by simp [c]
  have hctop : c ≠ ⊤ := by simp [c, hn0]
  set c' := c.toReal
  have hc' : 0 < c' := ENNReal.toReal_pos hc0 hctop
  have hG1 : μ G < 1 := by
    by_contra hcon
    push Not at hcon
    have hGc : μ Gᶜ = 0 := by
      rw [prob_compl_eq_one_sub hGm]; exact tsub_eq_zero_of_le hcon
    have : ν Eᶜ = 0 := hνμ (measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) hGc)
    rw [prob_compl_eq_zero_iff hE] at this
    exact hE1.ne this
  -- choice of `δ`
  set δ : ℝ := min (1 / 2) (ε * c' / (4 * C)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε * c' / (4 * C) := min_le_right _ _
  have hkey : C * δ < ε * (c' * (1 - δ)) := by
    have h1 : C * δ ≤ ε * c' / 4 := by
      calc C * δ ≤ C * (ε * c' / (4 * C)) := by gcongr
        _ = ε * c' / 4 := by field_simp
    have h2 : ε * c' / 2 ≤ ε * (c' * (1 - δ)) := by nlinarith [mul_pos hε hc']
    nlinarith [mul_pos hε hc']
  set T := {s | 1 - δ < privPost μ F G s} with hT_def
  have hTm : MeasurableSet T := measurableSet_lt measurable_const (measurable_privPost μ F hGm)
  have hTpos : 0 < signalLaw μ F T := (hTU G hGm hn hG1 δ hδ0).2
  set X := signalLaw μ F T
  have hXtop : X ≠ ⊤ := measure_ne_top _ _
  -- suppose the claim fails
  by_contra hzero
  have hzero' : signalLaw ν F {s | 1 - ε < privPost ν F E s} = 0 := by
    simpa using hzero
  have hpostc : ∀ᵐ s ∂(F ∘ₘ ν), ENNReal.ofReal ε ≤ (F†ν) s Eᶜ := by
    have : ∀ᵐ s ∂(signalLaw ν F), ¬ (1 - ε < privPost ν F E s) := by
      rw [ae_iff]; simpa using hzero'
    filter_upwards [this] with s hs
    push Not at hs
    have h1 : ε ≤ privPost ν F Eᶜ s := by rw [post_compl ν F hE]; linarith
    exact ENNReal.ofReal_le_of_le_toReal h1
  -- the lower chain
  have hlow : ENNReal.ofReal ε * signalLaw ν F T ≤ ENNReal.ofReal C * (ENNReal.ofReal δ * X) := by
    calc ENNReal.ofReal ε * signalLaw ν F T = ∫⁻ _s in T, ENNReal.ofReal ε ∂(F ∘ₘ ν) := by
          rw [setLIntegral_const]; rfl
      _ ≤ ∫⁻ s in T, (F†ν) s Eᶜ ∂(F ∘ₘ ν) := lintegral_mono_ae (ae_restrict_of_ae hpostc)
      _ = ∫⁻ ω in Eᶜ, F ω T ∂ν := (disint ν F hE.compl hTm).symm
      _ = ∫⁻ ω in Eᶜ, h ω * F ω T ∂μ := hνint hE.compl hTm
      _ ≤ ∫⁻ ω in Gᶜ, h ω * F ω T ∂μ :=
          lintegral_mono_set (Set.compl_subset_compl.2 Set.inter_subset_left)
      _ ≤ ∫⁻ ω in Gᶜ, ENNReal.ofReal C * F ω T ∂μ := by
          refine lintegral_mono_ae (ae_restrict_of_ae ?_)
          filter_upwards [hbound] with ω hω
          exact mul_le_mul_left hω _
      _ = ENNReal.ofReal C * ∫⁻ ω in Gᶜ, F ω T ∂μ :=
          lintegral_const_mul _ (Kernel.measurable_coe F hTm)
      _ = ENNReal.ofReal C * ∫⁻ s in T, (F†μ) s Gᶜ ∂(F ∘ₘ μ) := by rw [disint μ F hGm.compl hTm]
      _ ≤ ENNReal.ofReal C * ∫⁻ _s in T, ENNReal.ofReal δ ∂(F ∘ₘ μ) := by
          gcongr ENNReal.ofReal C * ?_
          refine lintegral_mono_ae ((ae_restrict_iff' hTm).2 (ae_of_all _ fun s hs => ?_))
          have h1 : privPost μ F Gᶜ s < δ := by
            rw [post_compl μ F hGm]; simp only [hT_def, Set.mem_ofPred_eq] at hs; linarith
          rw [← ENNReal.ofReal_toReal (measure_ne_top ((F†μ) s) Gᶜ)]
          exact ENNReal.ofReal_le_ofReal h1.le
      _ = ENNReal.ofReal C * (ENNReal.ofReal δ * X) := by
          rw [setLIntegral_const]; rfl
  -- the upper chain
  have hup : c * (ENNReal.ofReal (1 - δ) * X) ≤ signalLaw ν F T := by
    calc c * (ENNReal.ofReal (1 - δ) * X) = c * ∫⁻ _s in T, ENNReal.ofReal (1 - δ) ∂(F ∘ₘ μ) := by
          rw [setLIntegral_const]; rfl
      _ ≤ c * ∫⁻ s in T, (F†μ) s G ∂(F ∘ₘ μ) := by
          gcongr c * ?_
          refine lintegral_mono_ae ((ae_restrict_iff' hTm).2 (ae_of_all _ fun s hs => ?_))
          simp only [hT_def, Set.mem_ofPred_eq] at hs
          exact ENNReal.ofReal_le_of_le_toReal hs.le
      _ = c * ∫⁻ ω in G, F ω T ∂μ := by rw [disint μ F hGm hTm]
      _ = ∫⁻ ω in G, c * F ω T ∂μ := (lintegral_const_mul _ (Kernel.measurable_coe F hTm)).symm
      _ ≤ ∫⁻ ω in G, h ω * F ω T ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hGm).2 (ae_of_all _ fun ω hω => ?_))
          exact mul_le_mul_left hω.2.le _
      _ = ∫⁻ ω in G, F ω T ∂ν := (hνint hGm hTm).symm
      _ ≤ ∫⁻ ω, F ω T ∂ν := setLIntegral_le_lintegral _ _
      _ = signalLaw ν F T := by
          unfold signalLaw
          rw [Measure.bind_apply hTm (Kernel.aemeasurable _)]
  -- combine
  have hcomb : ENNReal.ofReal ε * (c * (ENNReal.ofReal (1 - δ) * X)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal δ * X) :=
    le_trans (mul_le_mul_right hup (ENNReal.ofReal ε)) hlow
  have hR := ENNReal.toReal_mono (by finiteness) hcomb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal hC.le,
    ENNReal.toReal_ofReal hδ0.le, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - δ)] at hR
  have hx : 0 < X.toReal := ENNReal.toReal_pos hTpos.ne' hXtop
  have : ε * (c' * (1 - δ)) * X.toReal ≤ C * δ * X.toReal := by
    calc ε * (c' * (1 - δ)) * X.toReal = ε * (c.toReal * ((1 - δ) * X.toReal)) := by ring
      _ ≤ C * (δ * X.toReal) := hR
      _ = C * δ * X.toReal := by ring
  have := le_of_mul_le_mul_right this hx
  linarith

end SSLLem5Aux

open SeqSocialLearning.Adequate SSLLem5Aux

theorem solution {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (hTU : TotallyUnbounded μ F)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ᵐ ω ∂μ, ν.rnDeriv μ ω ≤ ENNReal.ofReal C) :
    TotallyUnbounded ν F := by
  intro E hE h0 h1 ε hε
  refine ⟨?_, high μ F hTU ν hνμ C hC hbound hE h0 h1 hε⟩
  have hc0 : 0 < ν Eᶜ := by rw [prob_compl_eq_one_sub hE]; exact tsub_pos_of_lt h1
  have hc1 : ν Eᶜ < 1 := by
    rw [prob_compl_eq_one_sub hE]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero h0.ne'
  have := high μ F hTU ν hνμ C hC hbound hE.compl hc0 hc1 hε
  convert this using 2
  ext s
  simp only [Set.mem_ofPred_eq, post_compl ν F hE]
  constructor <;> intro h <;> linarith
