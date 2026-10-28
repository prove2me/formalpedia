-- Prove2me | solution 1 for WassersteinDRO.Regularization.coupling_upper_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:41:29.211782+00:00
-- url     : https://prove2.me/submissions/032d3cf7-6bad-41ff-b113-9ce5d30af38d

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory
open WassersteinDRO.Regularization

namespace WDROAux

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

lemma coupling_prob (π : Measure (E × E)) (Q : Measure E) [IsProbabilityMeasure Q]
    (h : π.map Prod.fst = Q) : IsProbabilityMeasure π := by
  constructor
  have := congrArg (fun μ : Measure E => μ Set.univ) h
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at this
  simpa using this

lemma keyA (f : E → ℝ) (hf : Measurable f) (Q P : Measure E) [IsProbabilityMeasure Q]
    (hQ : Integrable f Q) (hP : Integrable f P) (C : ENNReal) (hC : C ≠ ⊤)
    (hLip : ∀ a b, ENNReal.ofReal |f a - f b| ≤ C * ENNReal.ofReal ‖a - b‖)
    (π : Measure (E × E)) (h1 : π.map Prod.fst = Q) (h2 : π.map Prod.snd = P) :
    ENNReal.ofReal (∫ x, f x ∂Q - ∫ x, f x ∂P) ≤
      C * ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π := by
  have hπ := coupling_prob π Q h1
  have hQ' : Integrable (fun x : E × E => f x.1) π := by
    rw [← h1] at hQ; exact hQ.comp_measurable measurable_fst
  have hP' : Integrable (fun x : E × E => f x.2) π := by
    rw [← h2] at hP; exact hP.comp_measurable measurable_snd
  have e1 : ∫ x, f x ∂Q = ∫ x, f x.1 ∂π := by
    rw [← h1, integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
  have e2 : ∫ x, f x ∂P = ∫ x, f x.2 ∂π := by
    rw [← h2, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  rw [e1, e2, ← integral_sub hQ' hP']
  have hg : Integrable (fun x : E × E => f x.1 - f x.2) π := hQ'.sub hP'
  calc ENNReal.ofReal (∫ x, (f x.1 - f x.2) ∂π)
      ≤ ENNReal.ofReal (∫ x, |f x.1 - f x.2| ∂π) := by
        apply ENNReal.ofReal_le_ofReal
        exact integral_mono hg hg.abs (fun x => le_abs_self _)
    _ = ∫⁻ x, ENNReal.ofReal |f x.1 - f x.2| ∂π := by
        rw [ofReal_integral_eq_lintegral_ofReal hg.abs (ae_of_all _ fun x => abs_nonneg _)]
    _ ≤ ∫⁻ x, C * ENNReal.ofReal ‖x.1 - x.2‖ ∂π := lintegral_mono fun x => hLip x.1 x.2
    _ = C * ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π := lintegral_const_mul' _ _ hC

lemma keyB (f : E → ℝ) (hf : Measurable f) (Q P : Measure E) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P]
    (hQ : Integrable f Q) (hP : Integrable f P) (C : ENNReal) (hC : C ≠ ⊤)
    (hLip : ∀ a b, ENNReal.ofReal |f a - f b| ≤ C * ENNReal.ofReal ‖a - b‖) :
    ENNReal.ofReal (∫ x, f x ∂Q - ∫ x, f x ∂P) ≤
      C * ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π := by
  by_cases hC0 : C = 0
  · subst hC0
    have := keyA f hf Q P hQ hP 0 hC hLip (Q.prod P) (by simp) (by simp)
    simpa using this
  rw [ENNReal.mul_iInf_of_ne hC0 hC]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hC0 hC]
  refine le_iInf fun hπ => ?_
  exact keyA f hf Q P hQ hP C hC hLip π hπ.1 hπ.2

lemma empirical_prob {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) :
    IsProbabilityMeasure (empiricalDistribution ξhat) := by
  constructor
  simp only [empiricalDistribution, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

lemma eq_of_zero (Q P : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hW : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π) = 0) : Q = P := by
  -- integrals of thickened indicators agree
  have hint : ∀ (F : Set E) (δ : ℝ) (hδ : 0 < δ),
      ∫ x, (thickenedIndicator hδ F x : ℝ) ∂Q = ∫ x, (thickenedIndicator hδ F x : ℝ) ∂P := by
    intro F δ hδ
    have hL := lipschitzWith_thickenedIndicator hδ F
    set g : E → ℝ := fun x => (thickenedIndicator hδ F x : ℝ) with hg
    have gm : Measurable g := by
      have : Continuous g := by fun_prop
      exact this.measurable
    have hLg : ∀ a b, ENNReal.ofReal |g a - g b| ≤
        ((δ.toNNReal⁻¹ : NNReal) : ENNReal) * ENNReal.ofReal ‖a - b‖ := by
      intro a b
      have := hL.dist_le_mul a b
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← dist_eq_norm]
      simpa [g, NNReal.dist_eq] using this
    have hLg' : ∀ a b, ENNReal.ofReal |(-g) a - (-g) b| ≤
        ((δ.toNNReal⁻¹ : NNReal) : ENNReal) * ENNReal.ofReal ‖a - b‖ := by
      intro a b
      have := hLg a b
      simp only [Pi.neg_apply]
      rwa [show -g a - -g b = -(g a - g b) by ring, abs_neg]
    have iQ : Integrable g Q := integrable_thickenedIndicator F hδ
    have iP : Integrable g P := integrable_thickenedIndicator F hδ
    have k1 := keyB g gm Q P iQ iP _ ENNReal.coe_ne_top hLg
    have k2 := keyB (-g) gm.neg Q P iQ.neg iP.neg _ ENNReal.coe_ne_top hLg'
    rw [hW, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at k1 k2
    simp only [Pi.neg_apply, integral_neg] at k2
    show ∫ x, g x ∂Q = ∫ x, g x ∂P
    linarith
  have hclosed : ∀ F : Set E, IsClosed F → Q F = P F := by
    intro F hF
    have t1 := tendsto_integral_thickenedIndicator_of_isClosed Q hF
      (δs := fun n : ℕ => (1 : ℝ) / (n + 1)) (fun _ => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have t2 := tendsto_integral_thickenedIndicator_of_isClosed P hF
      (δs := fun n : ℕ => (1 : ℝ) / (n + 1)) (fun _ => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [hint] at t1
    have := tendsto_nhds_unique t1 t2
    rw [Measure.real_def, Measure.real_def] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F hF => hclosed F hF
  · exact hclosed _ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := E), borel_eq_generateFrom_isClosed]

end WDROAux

theorem solution {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → ℝ) (hm : Measurable ℓ)
    (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ : Integrable ℓ Q) (hP : Integrable ℓ (empiricalDistribution ξhat)) :
    ENNReal.ofReal (nominalRisk Q ℓ - nominalRisk (empiricalDistribution ξhat) ℓ) ≤
      lipschitzModulus ℓ * wassersteinDistance 1 Q (empiricalDistribution ξhat) := by
  have := WDROAux.empirical_prob hN ξhat
  set P := empiricalDistribution ξhat with hPdef
  have hW : wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π := by
    simp [wassersteinDistance]
  rw [hW]
  set L := lipschitzModulus ℓ with hLdef
  have hLip : ∀ a b, ENNReal.ofReal |ℓ a - ℓ b| ≤ L * ENNReal.ofReal ‖a - b‖ := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    have hn : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    have hle : ENNReal.ofReal (|ℓ a - ℓ b| / ‖a - b‖) ≤ L := by
      rw [hLdef, lipschitzModulus]
      exact le_iSup₂_of_le a b (le_iSup_of_le hab le_rfl)
    calc ENNReal.ofReal |ℓ a - ℓ b|
        = ENNReal.ofReal (|ℓ a - ℓ b| / ‖a - b‖) * ENNReal.ofReal ‖a - b‖ := by
          rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hn.ne']
      _ ≤ L * ENNReal.ofReal ‖a - b‖ := by gcongr
  unfold nominalRisk
  by_cases hLt : L = ⊤
  · by_cases hW0 : (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ x, ENNReal.ofReal ‖x.1 - x.2‖ ∂π) = 0
    · have hQP : Q = P := WDROAux.eq_of_zero Q P hW0
      rw [hQP]; simp
    · rw [hLt, ENNReal.top_mul hW0]; exact le_top
  · exact WDROAux.keyB ℓ hm Q P hQ hP L hLt hLip
