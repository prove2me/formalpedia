-- Prove2me | solution 1 for PalmQueueing.Ordering.strassen_cx
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T10:43:31.360026+00:00
-- url     : https://prove2.me/submissions/a224752b-04fb-429e-9646-addca46a1eef

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
/- Adapted from the accepted scalar Strassen closed-set and weighted-law proofs.
   The source space is a vector space and the integrand is a generic scalar weight,
   permitting both signs of every coordinate defect. -/
namespace MultivariateStrassenBorel
lemma closed_test_of_continuous_tests {d : ℕ}
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) → ℝ) (hwc : Continuous w) (hw : Integrable w μ)
    (ht : ∀ ψ : (Fin d → ℝ) →ᵇ ℝ, (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ z, ψ z.1*w z ∂μ)
    (s : Set (Fin d → ℝ)) (hs : IsClosed s) :
    0 ≤ ∫ z in Prod.fst ⁻¹' s, w z ∂μ := by
  let ψ : ℕ → (Fin d → ℝ) →ᵇ ℝ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (hs.apprSeq n x : ℝ))
    (NNReal.continuous_coe.comp (hs.apprSeq n).continuous) 1
    (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hs.apprSeq n x).coe_nonneg]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs n x)
  have hψnon : ∀ n x, 0 ≤ ψ n x := fun n x => (hs.apprSeq n x).coe_nonneg
  have hψle : ∀ n x, |ψ n x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (hψnon n x)]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs n x
  have hψlim : ∀ x, Tendsto (fun n => ψ n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := (NNReal.continuous_coe.tendsto (s.indicator (fun _ => (1 : ℝ≥0)) x)).comp
      (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) x)
    by_cases hx : x ∈ s <;> simpa [ψ,indicator,hx,Function.comp_def] using h
  have hlim : Tendsto (fun n => ∫ z, ψ n z.1*w z ∂μ) atTop
      (𝓝 (∫ z, (Prod.fst ⁻¹' s).indicator w z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => |w z|)
      (fun n => ((ψ n).continuous.comp continuous_fst).mul hwc |>.aestronglyMeasurable) hw.abs
    · intro n
      apply ae_of_all
      intro z
      simp only [Real.norm_eq_abs,Pi.mul_apply,Function.comp_apply]
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hψle n z.1) (abs_nonneg (w z))
    · apply ae_of_all
      intro z
      have he : s.indicator (fun _ => (1 : ℝ)) z.1*w z = (Prod.fst ⁻¹' s).indicator w z := by
        by_cases hz : z.1 ∈ s <;> simp [indicator,hz]
      simpa only [he,Pi.mul_apply,Function.comp_apply] using (hψlim z.1).mul (tendsto_const_nhds (x := w z))
  rw [integral_indicator (measurable_fst hs.measurableSet)] at hlim
  exact ge_of_tendsto' hlim (fun n => ht (ψ n) (hψnon n))

noncomputable def firstWeightedLaw {d : ℕ} (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (w : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  (μ.withDensity (fun z => ENNReal.ofReal (w z))).map Prod.fst

lemma firstWeightedLaw_finite {d : ℕ} (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (w : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (hw : Integrable w μ) (hwn : ∀ z, 0 ≤ w z) : IsFiniteMeasure (firstWeightedLaw μ w) := by
  have he := ofReal_integral_eq_lintegral_ofReal hw (ae_of_all _ hwn)
  have hi : (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≠ ⊤ := by rw [← he]; exact ENNReal.ofReal_ne_top
  letI := isFiniteMeasure_withDensity hi
  exact Measure.isFiniteMeasure_map _ _

lemma firstWeightedLaw_apply {d : ℕ} (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (w : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (hw : Integrable w μ) (hwn : ∀ z, 0 ≤ w z) (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    firstWeightedLaw μ w s = ENNReal.ofReal (∫ z in Prod.fst ⁻¹' s, w z ∂μ) := by
  rw [firstWeightedLaw, Measure.map_apply measurable_fst hs,
    withDensity_apply _ (measurable_fst hs)]
  exact (ofReal_integral_eq_lintegral_ofReal hw.integrableOn (ae_of_all _ hwn)).symm

lemma borel_test_of_closed_tests {d : ℕ}
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) → ℝ) (hw : Integrable w μ)
    (ht : ∀ s : Set (Fin d → ℝ), IsClosed s → 0 ≤ ∫ z in Prod.fst ⁻¹' s, w z ∂μ) :
    ∀ s : Set (Fin d → ℝ), MeasurableSet s → 0 ≤ ∫ z in Prod.fst ⁻¹' s, w z ∂μ := by
  let p : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun z => max (w z) 0
  let q : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun z => max (-(w z)) 0
  have hp : Integrable p μ := hw.pos_part
  have hq : Integrable q μ := hw.neg_part
  have hpn : ∀ z, 0 ≤ p z := fun z => le_max_right _ _
  have hqn : ∀ z, 0 ≤ q z := fun z => le_max_right _ _
  let M := firstWeightedLaw μ p
  let N := firstWeightedLaw μ q
  letI : IsFiniteMeasure M := firstWeightedLaw_finite μ p hp hpn
  letI : IsFiniteMeasure N := firstWeightedLaw_finite μ q hq hqn
  have hd : ∀ z : (Fin d → ℝ) × (Fin d → ℝ), p z - q z = w z := by
    intro z
    dsimp only [p, q]
    by_cases hz : 0 ≤ w z
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right (le_of_not_ge hz), max_eq_left (by linarith)]; ring
  have he : ∀ s : Set (Fin d → ℝ), (∫ z in Prod.fst ⁻¹' s, w z ∂μ) =
      (∫ z in Prod.fst ⁻¹' s, p z ∂μ) - ∫ z in Prod.fst ⁻¹' s, q z ∂μ := by
    intro s
    rw [← integral_sub hp.integrableOn hq.integrableOn]
    exact integral_congr_ae (ae_of_all _ (fun z => (hd z).symm))
  have hclosed : ∀ s : Set (Fin d → ℝ), IsClosed s → N s ≤ M s := by
    intro s hs
    have hi := ht s hs
    rw [he s] at hi
    change firstWeightedLaw μ q s ≤ firstWeightedLaw μ p s
    rw [firstWeightedLaw_apply μ q hq hqn s hs.measurableSet,
      firstWeightedLaw_apply μ p hp hpn s hs.measurableSet]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  intro s hs
  have hNM : N s ≤ M s := by
    rw [hs.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top N s)]
    refine iSup_le (fun K => iSup_le (fun hKs => iSup_le (fun hK => ?_)))
    exact (hclosed K hK).trans (measure_mono hKs)
  change firstWeightedLaw μ q s ≤ firstWeightedLaw μ p s at hNM
  rw [firstWeightedLaw_apply μ q hq hqn s hs, firstWeightedLaw_apply μ p hp hpn s hs] at hNM
  have hpos : 0 ≤ ∫ z in Prod.fst ⁻¹' s, p z ∂μ := integral_nonneg hpn
  have hreal := (ENNReal.ofReal_le_ofReal_iff hpos).mp hNM
  have hi : 0 ≤ ∫ z in Prod.fst ⁻¹' s, w z ∂μ := by rw [he s]; linarith
  exact hi

lemma borel_test_of_continuous_tests {d : ℕ}
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) → ℝ) (hwc : Continuous w) (hw : Integrable w μ)
    (ht : ∀ ψ : (Fin d → ℝ) →ᵇ ℝ, (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ z, ψ z.1*w z ∂μ) :
    ∀ s : Set (Fin d → ℝ), MeasurableSet s → 0 ≤ ∫ z in Prod.fst ⁻¹' s, w z ∂μ :=
  borel_test_of_closed_tests μ w hw (closed_test_of_continuous_tests μ w hwc hw ht)

lemma borel_eq_of_continuous_eq {d : ℕ}
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (w : ((Fin d → ℝ) × (Fin d → ℝ)) → ℝ) (hwc : Continuous w) (hw : Integrable w μ)
    (ht : ∀ ψ : (Fin d → ℝ) →ᵇ ℝ, (∫ z, ψ z.1*w z ∂μ) = 0) :
    ∀ s : Set (Fin d → ℝ), MeasurableSet s → (∫ z in Prod.fst ⁻¹' s, w z ∂μ) = 0 := by
  have hp := borel_test_of_continuous_tests μ w hwc hw (fun ψ _ => by rw [ht ψ])
  have hn := borel_test_of_continuous_tests μ (fun z => -w z) hwc.neg hw.neg
    (fun ψ _ => by simp only [mul_neg,integral_neg,ht ψ,neg_zero]; rfl)
  intro s hs
  have h₁ := hp s hs
  have h₂ := hn s hs
  rw [integral_neg] at h₂
  linarith
end MultivariateStrassenBorel
#print axioms MultivariateStrassenBorel.closed_test_of_continuous_tests
#print axioms MultivariateStrassenBorel.firstWeightedLaw_finite
#print axioms MultivariateStrassenBorel.firstWeightedLaw_apply
#print axioms MultivariateStrassenBorel.borel_test_of_closed_tests
#print axioms MultivariateStrassenBorel.borel_test_of_continuous_tests
#print axioms MultivariateStrassenBorel.borel_eq_of_continuous_eq

set_option autoImplicit false
open MeasureTheory
namespace MultivariateStrassenConditionalMean
lemma le_coord_condExp_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → Fin d → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P) (k : Fin d)
    (htests : ∀ s : Set (Fin d → ℝ), MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω k ∂P) ≤ ∫ ω in A ⁻¹' s, B ω k ∂P) :
    (fun ω => A ω k) ≤ᵐ[P] P[(fun ω => B ω k)|MeasurableSpace.comap A inferInstance] := by
  let m := MeasurableSpace.comap A inferInstance
  have hm : m ≤ mΩ := hmA.comap_le
  have hAm : StronglyMeasurable[m] (fun ω => A ω k) :=
    (continuous_apply k).comp_stronglyMeasurable (comap_measurable A).stronglyMeasurable
  have hCm : StronglyMeasurable[m] (P[(fun ω => B ω k)|m]) := stronglyMeasurable_condExp
  have htA := (hA.eval k).trim hm hAm
  have htC := (integrable_condExp (μ := P) (m := m) (f := fun ω => B ω k)).trim hm hCm
  have ht : (fun ω => A ω k) ≤ᵐ[P.trim hm] P[(fun ω => B ω k)|m] := by
    apply ae_le_of_forall_setIntegral_le htA htC
    intro s hs _
    rw [← setIntegral_trim hm hAm hs,← setIntegral_trim hm hCm hs,
      setIntegral_condExp hm (hB.eval k) hs]
    obtain ⟨t,ht,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    exact htests t ht
  exact ae_le_of_ae_le_trim ht

lemma eq_coord_condExp_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → Fin d → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P) (k : Fin d)
    (htests : ∀ s : Set (Fin d → ℝ), MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω k ∂P) = ∫ ω in A ⁻¹' s, B ω k ∂P) :
    (fun ω => A ω k) =ᵐ[P] P[(fun ω => B ω k)|MeasurableSpace.comap A inferInstance] := by
  let m := MeasurableSpace.comap A inferInstance
  have hm : m ≤ mΩ := hmA.comap_le
  have hAm : StronglyMeasurable[m] (fun ω => A ω k) :=
    (continuous_apply k).comp_stronglyMeasurable (comap_measurable A).stronglyMeasurable
  have hCm : StronglyMeasurable[m] (P[(fun ω => B ω k)|m]) := stronglyMeasurable_condExp
  have htA := (hA.eval k).trim hm hAm
  have htC := (integrable_condExp (μ := P) (m := m) (f := fun ω => B ω k)).trim hm hCm
  have ht : (fun ω => A ω k) =ᵐ[P.trim hm] P[(fun ω => B ω k)|m] := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ htA htC
    intro s hs _
    rw [← setIntegral_trim hm hAm hs,← setIntegral_trim hm hCm hs,
      setIntegral_condExp hm (hB.eval k) hs]
    obtain ⟨t,ht,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    exact htests t ht
  exact ae_eq_of_ae_eq_trim ht

lemma vector_condExp_eq_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → Fin d → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P)
    (htests : ∀ k (s : Set (Fin d → ℝ)), MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω k ∂P) = ∫ ω in A ⁻¹' s, B ω k ∂P) :
    P[B|MeasurableSpace.comap A inferInstance] =ᵐ[P] A := by
  have hh : ∀ k, ∀ᵐ ω ∂P, (P[B|MeasurableSpace.comap A inferInstance] ω) k = A ω k := by
    intro k
    have hc := (ContinuousLinearMap.proj k : (Fin d → ℝ) →L[ℝ] ℝ).comp_condExp_comm
      (m := MeasurableSpace.comap A inferInstance) hB
    have he := eq_coord_condExp_of_borel_tests P A B hmA hA hB k (htests k)
    filter_upwards [hc,he] with ω hω hω'
    exact hω.trans hω'.symm
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  exact funext hω

lemma vector_condExp_le_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → Fin d → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P)
    (htests : ∀ k (s : Set (Fin d → ℝ)), MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω k ∂P) ≤ ∫ ω in A ⁻¹' s, B ω k ∂P) :
    ∀ᵐ ω ∂P, PalmQueueing.Ordering.CoordLe (A ω) (P[B|MeasurableSpace.comap A inferInstance] ω) := by
  apply ae_all_iff.mpr
  intro k
  have hc := (ContinuousLinearMap.proj k : (Fin d → ℝ) →L[ℝ] ℝ).comp_condExp_comm
    (m := MeasurableSpace.comap A inferInstance) hB
  have he := le_coord_condExp_of_borel_tests P A B hmA hA hB k (htests k)
  filter_upwards [hc,he] with ω hω hω'
  exact hω'.trans_eq hω.symm
end MultivariateStrassenConditionalMean
#print axioms MultivariateStrassenConditionalMean.le_coord_condExp_of_borel_tests
#print axioms MultivariateStrassenConditionalMean.eq_coord_condExp_of_borel_tests
#print axioms MultivariateStrassenConditionalMean.vector_condExp_eq_of_borel_tests
#print axioms MultivariateStrassenConditionalMean.vector_condExp_le_of_borel_tests

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped BigOperators Topology
/- Adapted from the accepted scalar risk-order Strassen source. Norm moments,
   tightness, and law convergence are generalized to every finite vector dimension;
   pair moment bounds explicitly allow the two distinct original measures. -/
namespace MultivariateStrassenCompactness
lemma integral_norm_le_of_L1_close {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X A : Ω → Fin d → ℝ) (hX : Integrable X P) (hA : Integrable A P)
    (ε : ℝ) (he : (∫ ω, ‖X ω-A ω‖ ∂P) ≤ ε) :
    (∫ ω, ‖A ω‖ ∂P) ≤ (∫ ω, ‖X ω‖ ∂P)+ε := by
  have hb : ∀ ω, ‖A ω‖ ≤ ‖X ω‖+‖X ω-A ω‖ := by
    intro ω
    have hh := norm_add_le (X ω) (A ω-X ω)
    rw [add_sub_cancel] at hh
    simpa only [norm_sub_rev] using hh
  calc
    _ ≤ ∫ ω, ‖X ω‖+‖X ω-A ω‖ ∂P :=
      integral_mono hA.norm (hX.norm.add (hX.sub hA).norm) hb
    _ = (∫ ω, ‖X ω‖ ∂P)+(∫ ω, ‖X ω-A ω‖ ∂P) :=
      integral_add hX.norm (hX.sub hA).norm
    _ ≤ _ := add_le_add le_rfl he

lemma pair_moment_bound {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω') (X A : Ω → Fin d → ℝ) (Y B : Ω' → Fin d → ℝ)
    (hX : Integrable X P) (hY : Integrable Y Q) (hA : Integrable A P) (hB : Integrable B Q)
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hf : IdentDistrib Prod.fst A μ P) (hs : IdentDistrib Prod.snd B μ Q)
    (ε : ℝ) (heA : (∫ ω, ‖X ω-A ω‖ ∂P) ≤ ε) (heB : (∫ ω, ‖Y ω-B ω‖ ∂Q) ≤ ε) :
    Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) μ ∧
      (∫ z, ‖z‖ ∂μ) ≤ (∫ ω, ‖X ω‖ ∂P)+(∫ ω, ‖Y ω‖ ∂Q)+2*ε := by
  have hif : Integrable Prod.fst μ := hf.integrable_iff.mpr hA
  have his : Integrable Prod.snd μ := hs.integrable_iff.mpr hB
  have hn : ∀ z : (Fin d → ℝ) × (Fin d → ℝ), ‖z‖ ≤ ‖z.1‖+‖z.2‖ := by
    intro z
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hi : Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) μ :=
    (hif.norm.add his.norm).mono' continuous_norm.aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hn z))
  refine ⟨hi,?_⟩
  have hfabs := (hf.comp measurable_norm).integral_eq
  have hsabs := (hs.comp measurable_norm).integral_eq
  have hboundA := integral_norm_le_of_L1_close P X A hX hA ε heA
  have hboundB := integral_norm_le_of_L1_close Q Y B hY hB ε heB
  calc
    _ ≤ ∫ z, ‖z.1‖+‖z.2‖ ∂μ := integral_mono hi (hif.norm.add his.norm) hn
    _ = (∫ z, ‖z.1‖ ∂μ)+(∫ z, ‖z.2‖ ∂μ) := integral_add hif.norm his.norm
    _ = (∫ ω, ‖A ω‖ ∂P)+(∫ ω, ‖B ω‖ ∂Q) := congrArg₂ (· + ·) hfabs hsabs
    _ ≤ _ := by linarith

lemma tight_of_bounded_first_moment {d : ℕ} (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C) :
    IsTightMeasureSet (range (fun n => (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases he : ε = ⊤
  · subst ε; exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hepos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' he
  let r := (C + 1) / ε.toReal
  have hr : 0 < r := div_pos (by linarith) hepos
  have hre : r * ε.toReal = C + 1 := div_mul_cancel₀ _ hepos.ne'
  refine ⟨Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r, isCompact_closedBall _ _, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r)ᶜ ⊆ {z : (Fin d → ℝ) × (Fin d → ℝ) | r ≤ ‖z‖} := by
    intro z hz
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hmono := ENNReal.toReal_mono (measure_ne_top (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) _)
    (measure_mono hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) (ae_of_all _ (fun z => norm_nonneg z)) (hint n) r
  have hb : r * ((μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r)ᶜ).toReal ≤ C :=
    (mul_le_mul_of_nonneg_left hmono hr.le).trans (hmark.trans (hbound n))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) he).mp
  nlinarith

lemma subsequence_of_bounded_first_moment {d : ℕ} (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C) :
    ∃ ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have ht := tight_of_bounded_first_moment μ C hC hint hbound
  have hs : IsTightMeasureSet {((ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) | ν ∈ range μ} := by
    convert ht using 1
    ext ν
    simp only [mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨m, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, _, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hs).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩


lemma tendsto_eLpNorm_one_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (A n - X) 1 P) atTop (𝓝 0) := by
  have hn : ∀ n, eLpNorm (A n - X) 1 P = ENNReal.ofReal (∫ ω, ‖X ω - A n ω‖ ∂P) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm ((hA n).sub hX)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by simp [norm_sub_rev])
  simp_rw [hn]
  simpa using ENNReal.tendsto_ofReal he

lemma laws_tendsto_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    TendstoInDistribution A atTop X (fun _ => P) P := by
  have hn := tendsto_eLpNorm_one_of_L1 P X A hX hA he
  have hi := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1)
    (by norm_num) (by norm_num) (fun n => (hA n).aestronglyMeasurable)
    hX.aestronglyMeasurable hn
  exact hi.tendstoInDistribution (fun n => (hA n).aemeasurable)

lemma uniform_integrability_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    UnifIntegrable A 1 P := by
  exact unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num)
    (fun n => (memLp_one_iff_integrable.mpr (hA n))) (memLp_one_iff_integrable.mpr hX) (tendsto_eLpNorm_one_of_L1 P X A hX hA he)

lemma marginal_of_L1_weak_limit {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) (ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hweak : Tendsto (μ ∘ φ) atTop (𝓝 ν))
    (f : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ) (hf : Continuous f)
    (hmap : ∀ n, (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map f = P.map (A n)) :
    (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map f = P.map X := by
  have hd := laws_tendsto_of_L1 P X A hX hA he
  have hds := hd.tendsto.comp hφ.tendsto_atTop
  have hms := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (μ ∘ φ) ν hweak hf
  have heq : (fun n => ((μ ∘ φ) n).map hf.measurable.aemeasurable) =
      (fun n => (⟨P.map (A (φ n)), Measure.isProbabilityMeasure_map (hd.forall_aemeasurable (φ n))⟩ : ProbabilityMeasure (Fin d → ℝ))) := by
    funext n
    apply Subtype.ext
    exact hmap (φ n)
  rw [heq] at hms
  have hu := tendsto_nhds_unique hms hds
  exact congrArg Subtype.val hu

end MultivariateStrassenCompactness
#print axioms MultivariateStrassenCompactness.integral_norm_le_of_L1_close
#print axioms MultivariateStrassenCompactness.pair_moment_bound
#print axioms MultivariateStrassenCompactness.tight_of_bounded_first_moment
#print axioms MultivariateStrassenCompactness.subsequence_of_bounded_first_moment
#print axioms MultivariateStrassenCompactness.tendsto_eLpNorm_one_of_L1
#print axioms MultivariateStrassenCompactness.laws_tendsto_of_L1
#print axioms MultivariateStrassenCompactness.uniform_integrability_of_L1
#print axioms MultivariateStrassenCompactness.marginal_of_L1_weak_limit

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators Classical
/- Adapted from the accepted scalar convex-risk Strassen solution in the sibling workspace.
   The first five finite-law definitions/proofs are unchanged; representation and payoff
   are generalized from ℝ to an arbitrary measurable singleton space. -/
namespace MultivariateStrassenLaw
noncomputable def finiteLaw {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) : Measure α :=
  Measure.sum (fun i => ENNReal.ofReal (p i) • Measure.dirac (x i))

lemma finiteLaw_apply {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (s : Set α) :
    finiteLaw x p s = ∑ i, if x i ∈ s then ENNReal.ofReal (p i) else 0 := by
  classical
  simp [finiteLaw, Measure.sum_apply_of_countable, tsum_fintype, indicator_apply]

lemma finiteLaw_integrable {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (f : α → ℝ) : Integrable f (finiteLaw x p) := by
  apply integrable_sum_dirac (fun i => ENNReal.ofReal_ne_top)
  exact summable_of_hasFiniteSupport (Set.toFinite _)

lemma finiteLaw_integral {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (f : α → ℝ) :
    (∫ z, f z ∂finiteLaw x p) = ∑ i, p i * f (x i) := by
  rw [finiteLaw, integral_sum_dirac (fun i => ENNReal.ofReal_ne_top), tsum_fintype]
  simp [ENNReal.toReal_ofReal (hp _), smul_eq_mul]

lemma finiteLaw_probability {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteLaw x p) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hp
  rw [← hsum]
  exact hasSum_fintype p

lemma positive_atomic_representation {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ T : Finset α, T.Nonempty ∧
      (∀ a ∈ T, 0 < (μ {a}).toReal) ∧
      (∑ a ∈ T, (μ {a}).toReal) = 1 ∧
      μ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
  classical
  let T := S.filter (fun a => 0 < μ {a})
  have he : μ = ∑ a ∈ T, μ {a} • Measure.dirac a := by
    calc
      μ = ∑ a ∈ S, μ {a} • Measure.dirac a := Measure.ae_mem_finset_iff.mp hS
      _ = ∑ a ∈ T, μ {a} • Measure.dirac a := ?_
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro a ha hn
    have hz : μ {a} = 0 := by
      have : ¬0 < μ {a} := by simpa [T, ha] using hn
      exact le_zero_iff.mp (le_of_not_gt this)
    simp [hz]
  have hne : T.Nonempty := by
    by_contra hn
    have ht : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [ht] at he
    have hu := congrArg (fun ν : Measure α => ν univ) he
    simpa using hu
  have hpos : ∀ a ∈ T, 0 < (μ {a}).toReal := by
    intro a ha
    exact ENNReal.toReal_pos (mem_filter.mp ha).2.ne' (measure_ne_top _ _)
  have hrep : μ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
    calc
      μ = ∑ a ∈ T, μ {a} • Measure.dirac a := he
      _ = ∑ a : T, μ {(a : α)} • Measure.dirac (a : α) :=
        (Finset.sum_coe_sort T (fun a : α => μ {a} • Measure.dirac a)).symm
      _ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
        rw [finiteLaw, Measure.sum_fintype]
        apply sum_congr rfl
        intro a _
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨T, hne, hpos, ?_, hrep⟩
  have hi := finiteLaw_integral (fun a : T => (a : α))
    (fun a : T => (μ {(a : α)}).toReal) (fun a => ENNReal.toReal_nonneg) (fun _ => (1 : ℝ))
  rw [← hrep] at hi
  rw [← Finset.sum_coe_sort T (fun a : α => (μ {a}).toReal)]
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] using hi.symm

lemma finite_range_law {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → α) (hmA : Measurable A) (hFA : (range A).Finite) :
    ∃ T : Finset α, T.Nonempty ∧
      (∀ a ∈ T, 0 < ((P.map A) {a}).toReal) ∧
      (∑ a ∈ T, ((P.map A) {a}).toReal) = 1 ∧
      P.map A = finiteLaw (fun a : T => (a : α)) (fun a : T => ((P.map A) {(a : α)}).toReal) := by
  classical
  let : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hmA.aemeasurable
  let S := hFA.toFinset
  have hS : ∀ᵐ a ∂P.map A, a ∈ S := by
    apply (ae_map_iff hmA.aemeasurable S.measurableSet).mpr
    filter_upwards with ω
    change A ω ∈ hFA.toFinset
    exact hFA.mem_toFinset.mpr ⟨ω, rfl⟩
  exact positive_atomic_representation (P.map A) S hS

lemma payoff_of_finite_law {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype ι]
    (P : Measure Ω) (A : Ω → α) (hmA : Measurable A) (x : ι → α) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hrep : P.map A = finiteLaw x p)
    (φ : α → ℝ) (hφ : Measurable φ) :
    (∫ ω, φ (A ω) ∂P) = ∑ i, p i * φ (x i) := by
  calc
    (∫ ω, φ (A ω) ∂P) = ∫ z, φ z ∂P.map A :=
      (integral_map_of_stronglyMeasurable hmA hφ.stronglyMeasurable).symm
    _ = _ := by rw [hrep]; exact finiteLaw_integral x p hp φ

end MultivariateStrassenLaw
#print axioms MultivariateStrassenLaw.finiteLaw_apply
#print axioms MultivariateStrassenLaw.finiteLaw_integrable
#print axioms MultivariateStrassenLaw.finiteLaw_integral
#print axioms MultivariateStrassenLaw.finiteLaw_probability
#print axioms MultivariateStrassenLaw.positive_atomic_representation
#print axioms MultivariateStrassenLaw.finite_range_law
#print axioms MultivariateStrassenLaw.payoff_of_finite_law

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators Classical
open MultivariateStrassenLaw
namespace MultivariateStrassenPairs
lemma matrix_pair_law {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ) (p : ι → ℝ) (q : κ → ℝ) (c : ι → κ → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hrow : ∀ i, ∑ j, c i j = p i)
    (hcol : ∀ j, ∑ i, c i j = q j)
    (hp : ∑ i, p i = 1) :
    ∃ μ : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = finiteLaw x p ∧ μ.map Prod.snd = finiteLaw y q ∧
      ∀ f : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ,
        (∫ z, f z ∂μ) = ∑ i, ∑ j, c i j * f (x i,y j) := by
  classical
  let z : ι × κ → (Fin n → ℝ) × (Fin n → ℝ) := fun ij => (x ij.1, y ij.2)
  let w : ι × κ → ℝ := fun ij => c ij.1 ij.2
  let μ := finiteLaw z w
  have hw : ∀ ij, 0 ≤ w ij := fun ij => hc _ _
  have hsum : ∑ ij, w ij = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [w, hrow] using hp
  refine ⟨μ, finiteLaw_probability z w hw hsum, ?_, ?_, ?_⟩
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_fst hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    by_cases hi : x i ∈ s
    · simp only [z, w, Set.mem_preimage, hi, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc i j), hrow]
    · simp [z, w, hi]
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_snd hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases hj : y j ∈ s
    · simp only [z, w, Set.mem_preimage, hj, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i j), hcol]
    · simp [z, w, hj]
  · intro f
    simpa only [μ,z,w,Fintype.sum_prod_type] using finiteLaw_integral z w hw f
end MultivariateStrassenPairs
#print axioms MultivariateStrassenPairs.matrix_pair_law

set_option autoImplicit false
open Finset
open scoped BigOperators
namespace MultivariateStrassenDefect
lemma weighted_error_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d e h : ι → κ → ℝ) (M ε : ℝ) (hM : 0 ≤ M)
    (he : ∀ i k, 0 ≤ e i k) (hd : ∀ i k, |d i k| ≤ e i k)
    (hh : ∀ i k, |h i k| ≤ M) (hbudget : (∑ i, ∑ k, e i k) ≤ ε) :
    |∑ i, ∑ k, h i k*d i k| ≤ M*ε := by
  calc
    _ ≤ ∑ i, |∑ k, h i k*d i k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, |h i k*d i k| := sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, M*e i k := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro k _
      rw [abs_mul]
      exact mul_le_mul (hh i k) (hd i k) (abs_nonneg _) hM
    _ = M*(∑ i, ∑ k, e i k) := by simp only [mul_sum]
    _ ≤ M*ε := mul_le_mul_of_nonneg_left hbudget hM

lemma weighted_error_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d e h : ι → κ → ℝ) (M ε : ℝ) (hM : 0 ≤ M)
    (he : ∀ i k, 0 ≤ e i k) (hd : ∀ i k, -e i k ≤ d i k)
    (hh₀ : ∀ i k, 0 ≤ h i k) (hhM : ∀ i k, h i k ≤ M)
    (hbudget : (∑ i, ∑ k, e i k) ≤ ε) :
    -M*ε ≤ ∑ i, ∑ k, h i k*d i k := by
  have hp : ∀ i k, -(M*e i k) ≤ h i k*d i k := by
    intro i k
    have h₁ := mul_le_mul_of_nonneg_left (hd i k) (hh₀ i k)
    have h₂ := mul_le_mul_of_nonneg_right (hhM i k) (he i k)
    nlinarith
  have hs : (∑ i, ∑ k, -(M*e i k)) ≤ ∑ i, ∑ k, h i k*d i k :=
    sum_le_sum fun i _ => sum_le_sum fun k _ => hp i k
  have hb := mul_le_mul_of_nonneg_left hbudget hM
  simp only [sum_neg_distrib,← mul_sum] at hs
  linarith
end MultivariateStrassenDefect
#print axioms MultivariateStrassenDefect.weighted_error_bound
#print axioms MultivariateStrassenDefect.weighted_error_lower

set_option autoImplicit false
open scoped BigOperators
open Finset
open PalmQueueing.Ordering
namespace MultivariateStrassenFinite
noncomputable def dualEnvelope {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (t : Fin n → ℝ) : ℝ := by
  classical
  exact univ.sup' univ_nonempty (fun i => -a i - ∑ k, g i k * t k)

lemma dualEnvelope_convex {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) :
    ConvexOn ℝ Set.univ (dualEnvelope a g) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  unfold dualEnvelope
  apply sup'_le
  intro i _
  have hx := le_sup' (fun i => -a i - ∑ k, g i k*x k) (mem_univ i)
  have hy := le_sup' (fun i => -a i - ∑ k, g i k*y k) (mem_univ i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs : (∑ k, g i k*(u*x k+v*y k)) =
      u*(∑ k, g i k*x k)+v*(∑ k, g i k*y k) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  calc
    -a i - ∑ k, g i k*(u*x k+v*y k) =
        u*(-a i-∑ k, g i k*x k)+v*(-a i-∑ k, g i k*y k) := by
      rw [hs]
      linear_combination a i * huv
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)

lemma dualEnvelope_coordMonotone {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (hg : ∀ i k, g i k ≤ 0) :
    ∀ x y, CoordLe x y → dualEnvelope a g x ≤ dualEnvelope a g y := by
  classical
  intro x y hxy
  unfold dualEnvelope
  apply sup'_le
  intro i _
  apply le_trans ?_ (le_sup' (fun i => -a i - ∑ k, g i k*y k) (mem_univ i))
  have hs : (∑ k, g i k*y k) ≤ ∑ k, g i k*x k :=
    sum_le_sum fun k _ => mul_le_mul_of_nonpos_left (hxy k) (hg i k)
  linarith

lemma dualEnvelope_mem_classCx {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) : dualEnvelope a g ∈ classCx n :=
  dualEnvelope_convex a g

lemma dualEnvelope_mem_classIcx {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (hg : ∀ i k, g i k ≤ 0) :
    dualEnvelope a g ∈ classIcx n :=
  ⟨dualEnvelope_coordMonotone a g hg, dualEnvelope_convex a g⟩
end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.dualEnvelope_convex
#print axioms MultivariateStrassenFinite.dualEnvelope_coordMonotone
#print axioms MultivariateStrassenFinite.dualEnvelope_mem_classCx
#print axioms MultivariateStrassenFinite.dualEnvelope_mem_classIcx

set_option autoImplicit false
open MeasureTheory Set
namespace MultivariateStrassenApproximation
lemma integrable_identity {n : ℕ} (F : Measure (Fin n → ℝ))
    (hF : PalmQueueing.Ordering.IsIntegrableDist F) :
    Integrable (fun x : Fin n → ℝ => x) F :=
  (integrable_norm_iff (by fun_prop)).mp hF

lemma exists_vector_simple_L1 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Fin n → ℝ) (hX : Integrable X P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : SimpleFunc Ω (Fin n → ℝ), Integrable s P ∧
      (∫ ω, ‖X ω - s ω‖ ∂P) < ε := by
  have hm : MemLp X 1 P := memLp_one_iff_integrable.mpr hX
  obtain ⟨s,hs,hsm⟩ := hm.exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hε)
  have hi := memLp_one_iff_integrable.mp hsm
  refine ⟨s,hi,?_⟩
  have hreal := ENNReal.toReal_lt_of_lt_ofReal hs
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    (hX.sub hi).aestronglyMeasurable] at hreal
  exact hreal

lemma exists_identity_finite_L1 {n : ℕ} (F : Measure (Fin n → ℝ))
    (hF : PalmQueueing.Ordering.IsIntegrableDist F) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : (Fin n → ℝ) → Fin n → ℝ, Measurable A ∧ (range A).Finite ∧
      Integrable A F ∧ (∫ x, ‖x-A x‖ ∂F) < ε := by
  obtain ⟨s,hs,he⟩ := exists_vector_simple_L1 F (fun x => x) (integrable_identity F hF) ε hε
  exact ⟨s,s.measurable,s.finite_range,hs,he⟩
end MultivariateStrassenApproximation
#print axioms MultivariateStrassenApproximation.integrable_identity
#print axioms MultivariateStrassenApproximation.exists_vector_simple_L1
#print axioms MultivariateStrassenApproximation.exists_identity_finite_L1

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory
namespace MultivariateStrassenFinite
lemma finite_sup_integrable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) P) :
    Integrable (fun ω => univ.sup' univ_nonempty (fun i => f i ω)) P := by
  classical
  have hmain : ∀ (s : Finset ι) (hs : s.Nonempty),
      Integrable (fun ω => s.sup' hs (fun i => f i ω)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact False.elim (not_nonempty_empty hs)
    | insert i s hnot ih =>
      intro hs
      by_cases hS : s.Nonempty
      · simp_rw [sup'_insert hS]
        exact (hf i).sup (ih hS)
      · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hS
        subst s
        simpa using hf i
  exact hmain univ univ_nonempty

lemma dualEnvelope_comp_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {ι : Type*} [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Fin n → ℝ) (hX : Integrable X P) (a : ι → ℝ) (g : ι → Fin n → ℝ) :
    Integrable (fun ω => dualEnvelope a g (X ω)) P := by
  apply finite_sup_integrable
  intro i
  have hs : Integrable (fun ω => ∑ k, g i k*X ω k) P := by
    apply integrable_finsetSum
    intro k _
    exact (hX.eval k).const_mul (g i k)
  exact (integrable_const (-a i)).sub hs

lemma dualEnvelope_integrable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Measure (Fin n → ℝ)) [IsFiniteMeasure F]
    (hF : PalmQueueing.Ordering.IsIntegrableDist F)
    (a : ι → ℝ) (g : ι → Fin n → ℝ) : Integrable (dualEnvelope a g) F := by
  have hid := MultivariateStrassenApproximation.integrable_identity F hF
  apply finite_sup_integrable
  intro i
  have hs : Integrable (fun x => ∑ k, g i k*x k) F := by
    apply integrable_finsetSum
    intro k _
    exact (hid.eval k).const_mul (g i k)
  exact (integrable_const (-a i)).sub hs
end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.finite_sup_integrable
#print axioms MultivariateStrassenFinite.dualEnvelope_integrable

#print axioms MultivariateStrassenFinite.dualEnvelope_comp_integrable

set_option autoImplicit false
open scoped BigOperators
open Finset
namespace MultivariateStrassenFinite
lemma affine_sum_error {n : ℕ} (g : Fin n → ℝ) (C : ℝ)
    (hg : ∀ k, |g k| ≤ C) (x y : Fin n → ℝ) :
    |∑ k, g k*(x k-y k)| ≤ C * ∑ k, |x k-y k| := by
  calc
    _ ≤ ∑ k, |g k*(x k-y k)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, C*|x k-y k| := sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hg k) (abs_nonneg _)
    _ = _ := (mul_sum _ _ _).symm

lemma dualEnvelope_one_sided_error {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hg : ∀ i k, |g i k| ≤ C) (x y : Fin n → ℝ) :
    dualEnvelope a g x ≤ dualEnvelope a g y + C*(∑ k, |x k-y k|) := by
  classical
  unfold dualEnvelope
  apply sup'_le
  intro i _
  have hy := le_sup' (fun i => -a i-∑ k, g i k*y k) (mem_univ i)
  have hs := affine_sum_error (g i) C (hg i) x y
  have hl := neg_le_abs (∑ k, g i k*(x k-y k))
  have he : (∑ k, g i k*(x k-y k)) = (∑ k, g i k*x k)-(∑ k, g i k*y k) := by
    simp only [mul_sub,sum_sub_distrib]
  rw [he] at hs hl
  linarith

lemma dualEnvelope_absolute_error {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hg : ∀ i k, |g i k| ≤ C) (x y : Fin n → ℝ) :
    |dualEnvelope a g x-dualEnvelope a g y| ≤ C*(∑ k, |x k-y k|) := by
  have hxy := dualEnvelope_one_sided_error a g C hg x y
  have hyx := dualEnvelope_one_sided_error a g C hg y x
  have he : (∑ k, |y k-x k|) = ∑ k, |x k-y k| := by simp only [abs_sub_comm]
  rw [he] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma coord_distance_le_norm {n : ℕ} (x y : Fin n → ℝ) :
    (∑ k, |x k-y k|) ≤ n*‖x-y‖ := by
  calc
    _ ≤ ∑ _k : Fin n, ‖x-y‖ := sum_le_sum fun k _ => by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (x-y) k
    _ = _ := by simp
end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.affine_sum_error
#print axioms MultivariateStrassenFinite.dualEnvelope_one_sided_error
#print axioms MultivariateStrassenFinite.dualEnvelope_absolute_error
#print axioms MultivariateStrassenFinite.coord_distance_le_norm

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace MultivariateStrassenFinite
lemma integral_dualEnvelope_approx_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X A : Ω → Fin n → ℝ) (hX : Integrable X P) (hA : Integrable A P)
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ i k, |g i k| ≤ C) :
    (∫ ω, dualEnvelope a g (A ω) ∂P) ≤
      (∫ ω, dualEnvelope a g (X ω) ∂P) +
        C*(n : ℝ)*(∫ ω, ‖A ω-X ω‖ ∂P) := by
  have hiA := dualEnvelope_comp_integrable P A hA a g
  have hiX := dualEnvelope_comp_integrable P X hX a g
  have hiD := (hA.sub hX).norm.const_mul (C*(n : ℝ))
  change Integrable (fun ω => (C*(n : ℝ))*‖A ω-X ω‖) P at hiD
  have hpoint : ∀ ω, dualEnvelope a g (A ω) ≤
      dualEnvelope a g (X ω) + (C*(n : ℝ))*‖A ω-X ω‖ := by
    intro ω
    have h₁ := dualEnvelope_one_sided_error a g C hg (A ω) (X ω)
    have h₂ := mul_le_mul_of_nonneg_left (coord_distance_le_norm (A ω) (X ω)) hC
    nlinarith
  have hh := integral_mono hiA (hiX.add hiD) hpoint
  change (∫ ω, dualEnvelope a g (A ω) ∂P) ≤
    ∫ ω, dualEnvelope a g (X ω) + (C*(n : ℝ))*‖A ω-X ω‖ ∂P at hh
  rw [integral_add hiX hiD, integral_const_mul] at hh
  exact hh

lemma integral_dualEnvelope_order_approx {n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (F G : Measure (Fin n → ℝ)) [IsFiniteMeasure F] [IsFiniteMeasure G]
    (hF : PalmQueueing.Ordering.IsIntegrableDist F)
    (hG : PalmQueueing.Ordering.IsIntegrableDist G)
    (A B : (Fin n → ℝ) → Fin n → ℝ)
    (hA : Integrable A F) (hB : Integrable B G)
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ i k, |g i k| ≤ C)
    (horder : (∫ x, dualEnvelope a g x ∂F) ≤ ∫ y, dualEnvelope a g y ∂G) :
    (∫ x, dualEnvelope a g (A x) ∂F) ≤
      (∫ y, dualEnvelope a g (B y) ∂G) +
        C*(n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G)) := by
  have h₁ := integral_dualEnvelope_approx_le F id A
    (MultivariateStrassenApproximation.integrable_identity F hF) hA a g C hC hg
  have h₂ := integral_dualEnvelope_approx_le G B id hB
    (MultivariateStrassenApproximation.integrable_identity G hG) a g C hC hg
  simp only [id_eq, norm_sub_rev (A _)] at h₁
  simp only [id_eq] at h₂
  nlinarith
lemma cx_dualEnvelope_order_approx {n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (F G : Measure (Fin n → ℝ)) [IsFiniteMeasure F] [IsFiniteMeasure G]
    (hF : PalmQueueing.Ordering.IsIntegrableDist F)
    (hG : PalmQueueing.Ordering.IsIntegrableDist G)
    (horder : PalmQueueing.Ordering.CxLe F G)
    (A B : (Fin n → ℝ) → Fin n → ℝ)
    (hA : Integrable A F) (hB : Integrable B G)
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ i k, |g i k| ≤ C) :
    (∫ x, dualEnvelope a g (A x) ∂F) ≤
      (∫ y, dualEnvelope a g (B y) ∂G) +
        C*(n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G)) := by
  apply integral_dualEnvelope_order_approx F G hF hG A B hA hB a g C hC hg
  exact horder _ (dualEnvelope_mem_classCx a g)
    (dualEnvelope_integrable F hF a g) (dualEnvelope_integrable G hG a g)

lemma icx_dualEnvelope_order_approx {n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (F G : Measure (Fin n → ℝ)) [IsFiniteMeasure F] [IsFiniteMeasure G]
    (hF : PalmQueueing.Ordering.IsIntegrableDist F)
    (hG : PalmQueueing.Ordering.IsIntegrableDist G)
    (horder : PalmQueueing.Ordering.IcxLe F G)
    (A B : (Fin n → ℝ) → Fin n → ℝ)
    (hA : Integrable A F) (hB : Integrable B G)
    (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ i k, |g i k| ≤ C) (hneg : ∀ i k, g i k ≤ 0) :
    (∫ x, dualEnvelope a g (A x) ∂F) ≤
      (∫ y, dualEnvelope a g (B y) ∂G) +
        C*(n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G)) := by
  apply integral_dualEnvelope_order_approx F G hF hG A B hA hB a g C hC hg
  exact horder _ (dualEnvelope_mem_classIcx a g hneg)
    (dualEnvelope_integrable F hF a g) (dualEnvelope_integrable G hG a g)

end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.integral_dualEnvelope_approx_le
#print axioms MultivariateStrassenFinite.integral_dualEnvelope_order_approx

#print axioms MultivariateStrassenFinite.cx_dualEnvelope_order_approx
#print axioms MultivariateStrassenFinite.icx_dualEnvelope_order_approx

set_option autoImplicit false
open scoped BigOperators
namespace RiskOrderFinite.Duality

/-!
# Finitely generated convex cones and primitive cones

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007,
§6.4, p. 89 (convex cone generated by `a₁, …, aₙ`) and §6.5, p. 96 (primitive cone).
Points of `ℝ^m` are elements of `EuclideanSpace ℝ (Fin m)`, so distances are Euclidean.
-/

variable {m n : ℕ}

/-- The **convex cone generated by** `a₁, …, aₙ ∈ ℝ^m` (p. 89): the set of all linear
combinations `t₁a₁ + ⋯ + tₙaₙ` with `t₁, …, tₙ ≥ 0`.  For `n = 0` it is `{0}`. -/
def coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ t : Fin n → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • a i}

/-- A **primitive cone** in `ℝ^m` (p. 96): a convex cone generated by some `k ≤ m` linearly
independent vectors (`k = 0` gives `{0}`). -/
def IsPrimitiveCone (P : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ v : Fin k → EuclideanSpace ℝ (Fin m),
    LinearIndependent ℝ v ∧ P = coneGen v

end RiskOrderFinite.Duality

open Finset

namespace RiskOrderConicCara

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- Conic Carathéodory: a nonnegative combination of `a` is a nonnegative combination of a
linearly independent subfamily. -/
theorem exists_linIndep_repr (a : Fin n → E) :
    ∀ (k : ℕ) (t : Fin n → ℝ), (∀ i, 0 ≤ t i) → (univ.filter fun i => t i ≠ 0).card ≤ k →
      ∃ (S : Finset (Fin n)) (s : Fin n → ℝ), (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
        LinearIndependent ℝ (fun i : S => a i) ∧ ∑ i, s i • a i = ∑ i, t i • a i := by
  intro k
  induction k with
  | zero =>
    intro t ht hk
    refine ⟨∅, t, ht, fun i _ => ?_, linearIndependent_empty_type, rfl⟩
    by_contra h
    have : i ∈ univ.filter fun i => t i ≠ 0 := by simp [h]
    simp_all
  | succ k ih =>
    intro t ht hk
    set T := univ.filter fun i => t i ≠ 0 with hT
    by_cases hli : LinearIndependent ℝ (fun i : T => a i)
    · refine ⟨T, t, ht, fun i hi => ?_, hli, rfl⟩
      by_contra h; exact hi (by simp [T, h])
    · -- a nontrivial dependency supported on T
      obtain ⟨g, hg, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hli
      -- extend to Fin n, possibly negating so that some coefficient is positive
      have hpos : ∃ μ : Fin n → ℝ, (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • a i = 0 ∧ ∃ i, 0 < μ i := by
        set μ0 : Fin n → ℝ := fun i => if h : i ∈ T then g ⟨i, h⟩ else 0
        have hsum : ∑ i, μ0 i • a i = 0 := by
          rw [← hg]
          rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by simp [μ0, hi])]
          rw [← Finset.sum_coe_sort T]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [μ0, i.2]
        have hsupp : ∀ i, i ∉ T → μ0 i = 0 := fun i hi => by simp [μ0, hi]
        have hj' : μ0 j ≠ 0 := by simp [μ0, j.2, hj]
        rcases lt_or_gt_of_ne hj' with hneg | hpos
        · refine ⟨-μ0, fun i hi => by simp [hsupp i hi], by simp [neg_smul, hsum], j, by simpa using hneg⟩
        · exact ⟨μ0, hsupp, hsum, j, hpos⟩
      obtain ⟨μ, hμT, hμsum, i₀, hi₀⟩ := hpos
      -- choose the ratio-minimizing positive coordinate
      set P := univ.filter fun i => 0 < μ i
      have hPne : P.Nonempty := ⟨i₀, by simp [P, hi₀]⟩
      obtain ⟨j₀, hj₀P, hj₀min⟩ := P.exists_min_image (fun i => t i / μ i) hPne
      have hμj₀ : 0 < μ j₀ := (Finset.mem_filter.mp hj₀P).2
      set θ := t j₀ / μ j₀
      have hθ : 0 ≤ θ := div_nonneg (ht j₀) hμj₀.le
      set t' : Fin n → ℝ := fun i => t i - θ * μ i
      have ht' : ∀ i, 0 ≤ t' i := by
        intro i
        by_cases hi : 0 < μ i
        · have := hj₀min i (by simp [P, hi])
          rw [div_le_div_iff₀ hμj₀ hi] at this
          simp only [t', sub_nonneg, θ]
          rw [div_mul_eq_mul_div, div_le_iff₀ hμj₀]
          linarith
        · push_neg at hi
          simp only [t']
          nlinarith [ht i]
      have ht'j₀ : t' j₀ = 0 := by simp [t', θ, div_mul_cancel₀ _ hμj₀.ne']
      have hsubset : (univ.filter fun i => t' i ≠ 0) ⊆ T := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hti
        apply hi
        have hti' : t i = 0 := by simpa [T] using hti
        have hμi : μ i = 0 := hμT i hti
        simp [t', hti', hμi]
      have hj₀T : j₀ ∈ T := by
        by_contra h
        have hμj₀0 : μ j₀ = 0 := hμT j₀ h
        linarith
      have hsub : (univ.filter fun i => t' i ≠ 0) ⊂ T :=
        (Finset.ssubset_iff_of_subset hsubset).mpr ⟨j₀, hj₀T, by simp [ht'j₀]⟩
      have hcard : (univ.filter fun i => t' i ≠ 0).card ≤ k := by
        have := Finset.card_lt_card hsub; omega
      obtain ⟨S, s, hs, hsS, hSli, hsum⟩ := ih t' ht' hcard
      refine ⟨S, s, hs, hsS, hSli, ?_⟩
      rw [hsum]
      simp only [t', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμsum,
        smul_zero, sub_zero]

end RiskOrderConicCara

namespace RiskOrderConeAux

open RiskOrderFinite.Duality

variable {m n : ℕ}

/-- The cone generated by the subfamily indexed by `S`, as supported combinations. -/
def subCone (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ s : Fin n → ℝ, (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧ x = ∑ i, s i • a i}

lemma subCone_subset (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    subCone a S ⊆ coneGen a := by
  rintro x ⟨s, hs, -, rfl⟩; exact ⟨s, hs, rfl⟩

/-- A linearly independent subfamily generates a primitive cone. -/
lemma subCone_primitive (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (hS : LinearIndependent ℝ (fun i : S => a i)) : IsPrimitiveCone (subCone a S) := by
  classical
  set σ : Fin S.card ≃o S := S.orderIsoOfFin rfl
  set v : Fin S.card → EuclideanSpace ℝ (Fin m) := fun r => a (σ r)
  have hv : LinearIndependent ℝ v := hS.comp σ σ.injective
  refine ⟨S.card, ?_, v, hv, ?_⟩
  · have := hv.fintype_card_le_finrank
    simpa using this
  · ext x
    constructor
    · rintro ⟨s, hs, hsS, rfl⟩
      refine ⟨fun r => s (σ r), fun r => hs _, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hsS i hi])]
      rw [← Finset.sum_coe_sort S]
      exact (Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)).symm
    · rintro ⟨t, ht, rfl⟩
      set s : Fin n → ℝ := fun i => if h : i ∈ S then t (σ.symm ⟨i, h⟩) else 0
      refine ⟨s, fun i => ?_, fun i hi => by simp [s, hi], ?_⟩
      · simp only [s]; split_ifs <;> simp [ht]
      · rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [s, hi])]
        rw [← Finset.sum_coe_sort S]
        rw [← Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [s, v]

/-- Every finitely generated cone is the union of the primitive cones of its linearly independent
subfamilies. -/
lemma coneGen_eq_iUnion (a : Fin n → EuclideanSpace ℝ (Fin m)) :
    coneGen a = ⋃ (S : Finset (Fin n)) (_ : LinearIndependent ℝ (fun i : S => a i)),
      subCone a S := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, s, hs, hsS, hli, hsum⟩ :=
      RiskOrderConicCara.exists_linIndep_repr a _ t ht le_rfl
    exact ⟨S, hli, s, hs, hsS, hsum.symm⟩
  · rintro ⟨S, -, hx⟩; exact subCone_subset a S hx

lemma isClosed_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : IsClosed (coneGen a) := by
  classical
  rw [coneGen_eq_iUnion]
  refine isClosed_iUnion_of_finite fun S => isClosed_iUnion_of_finite fun hli => ?_
  obtain ⟨k, -, v, hv, hP⟩ := subCone_primitive a S hli
  rw [hP]
  -- a primitive cone is closed (image of the orthant under a closed embedding)
  set L : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ v
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  have himage : coneGen v = L '' {t | ∀ i, 0 ≤ t i} := by
    ext x
    simp only [coneGen, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
  rw [himage]
  apply (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap
  have : {t : Fin k → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t | 0 ≤ t i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma zero_mem_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : (0 : _) ∈ coneGen a :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma convex_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Convex ℝ (coneGen a) := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ α β hα hβ -
  refine ⟨fun i => α * s i + β * t i, fun i => by have := hs i; have := ht i; positivity, ?_⟩
  simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]

end RiskOrderConeAux

open RiskOrderFinite.Duality RiskOrderConeAux in
theorem riskOrderFarkasGeometric {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    Xor (b ∈ coneGen a)
      (∃ y : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ inner ℝ y (a i)) ∧ inner ℝ y b < 0) := by
  by_cases hb : b ∈ coneGen a
  · -- no separating vector exists
    refine Or.inl ⟨hb, ?_⟩
    rintro ⟨y, hy, hyb⟩
    obtain ⟨t, ht, rfl⟩ := hb
    have : 0 ≤ inner ℝ y (∑ i, t i • a i) := by
      rw [inner_sum]
      exact Finset.sum_nonneg fun i _ => by rw [inner_smul_right]; exact mul_nonneg (ht i) (hy i)
    linarith
  · refine Or.inr ⟨?_, hb⟩
    -- nearest point z of the closed convex cone; y = z - b separates
    obtain ⟨z, hz, hdist⟩ := (isClosed_coneGen a).exists_infDist_eq_dist ⟨0, zero_mem_coneGen a⟩ b
    have hmin : ‖b - z‖ = ⨅ w : coneGen a, ‖b - w‖ := by
      rw [← dist_eq_norm, ← hdist, Metric.infDist_eq_iInf]
      simp [dist_eq_norm]
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_coneGen a) hz).mp hmin
    -- variational inequality: ⟪b - z, w - z⟫ ≤ 0 for all w in the cone
    have hai : ∀ i, inner ℝ (b - z) (a i) ≤ 0 := by
      intro i
      obtain ⟨s, hs, rfl⟩ := hz
      have hw : (∑ j, s j • a j) + a i ∈ coneGen a :=
        ⟨fun j => s j + if j = i then 1 else 0, fun j => by
          show 0 ≤ s j + (if j = i then (1 : ℝ) else 0)
          have := hs j; split_ifs <;> linarith,
          by simp [add_smul, Finset.sum_add_distrib, Finset.sum_ite_eq']⟩
      simpa using hvar _ hw
    have hz0 : inner ℝ (b - z) z = 0 := by
      have h0 := hvar 0 (zero_mem_coneGen a)
      have h2 : (2 : ℝ) • z ∈ coneGen a := by
        obtain ⟨s, hs, hzs⟩ := hz
        exact ⟨fun j => 2 * s j, fun j => by have := hs j; positivity, by
          simp [hzs, Finset.smul_sum, mul_smul]⟩
      have h2' := hvar _ h2
      simp only [zero_sub, inner_neg_right] at h0
      rw [show (2 : ℝ) • z - z = z by module] at h2'
      linarith
    have hne : b - z ≠ 0 := by
      intro h; apply hb; rw [sub_eq_zero.mp h]; exact hz
    refine ⟨z - b, fun i => ?_, ?_⟩
    · have := hai i
      rw [show z - b = -(b - z) by abel, inner_neg_left]; linarith
    · have hpos : 0 < inner ℝ (b - z) (b - z) := real_inner_self_pos.mpr hne
      have hsplit : inner ℝ (b - z) b = inner ℝ (b - z) (b - z) + inner ℝ (b - z) z := by
        rw [← inner_add_right]; congr 1; abel
      rw [show z - b = -(b - z) by abel, inner_neg_left, hsplit, hz0]
      linarith

namespace RiskOrderFarkas

open Matrix RiskOrderFinite.Duality RiskOrderConeAux

/-- Farkas' lemma, equational form: `Ax = b, x ≥ 0` is solvable iff every `y` with `Aᵀy ≥ 0`
has `yᵀb ≥ 0`. -/
theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases riskOrderFarkasGeometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith


/-- `farkas_eq` for an arbitrary finite column index. -/
theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp


/-- Farkas, equational form, arbitrary finite row and column index types. -/
theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

end RiskOrderFarkas
#print axioms RiskOrderFarkas.farkas_eq_gen

set_option autoImplicit false
open scoped BigOperators
open Matrix Finset PalmQueueing.Ordering
namespace MultivariateStrassenFinite
noncomputable def vectorMatrix {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (slack : Bool) (y : κ → Fin n → ℝ) :
    Matrix (ι ⊕ (κ ⊕ (ι × Fin n))) ((ι × κ) ⊕ (ι × Fin n)) ℝ := by
  classical
  exact fun r c => match r,c with
    | Sum.inl k, Sum.inl (i,_) => if k=i then 1 else 0
    | Sum.inr (Sum.inl k), Sum.inl (_,j) => if k=j then 1 else 0
    | Sum.inr (Sum.inr k), Sum.inl (i,j) => if k.1=i then y j k.2 else 0
    | Sum.inr (Sum.inr k), Sum.inr l => if k=l then (if slack then -1 else 0) else 0
    | _,_ => 0

def vectorRhs {n : ℕ} {ι κ : Type*} (x : ι → Fin n → ℝ) (p : ι → ℝ) (q : κ → ℝ) :
    (ι ⊕ (κ ⊕ (ι × Fin n))) → ℝ
  | Sum.inl i => p i
  | Sum.inr (Sum.inl j) => q j
  | Sum.inr (Sum.inr k) => x k.1 k.2*p k.1

lemma finite_vector_feasible {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ φ : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ φ →
      (slack = true → ∀ r s, CoordLe r s → φ r ≤ φ s) →
      (∑ i, p i*φ (x i)) ≤ ∑ j, q j*φ (y j)) :
    ∃ z : ((ι × κ) ⊕ (ι × Fin n)) → ℝ,
      0 ≤ z ∧ vectorMatrix slack y *ᵥ z = vectorRhs x p q := by
  classical
  let A := vectorMatrix (ι := ι) slack y
  let b := vectorRhs x p q
  apply (RiskOrderFarkas.farkas_eq_gen A b).mpr
  intro w hw
  let a : ι → ℝ := fun i => w (Sum.inl i)
  let d : κ → ℝ := fun j => w (Sum.inr (Sum.inl j))
  let g : ι → Fin n → ℝ := fun i k => w (Sum.inr (Sum.inr (i,k)))
  have hg : slack = true → ∀ i k, g i k ≤ 0 := by
    intro ht i k
    have hh := hw (Sum.inr (i,k))
    simpa [A, vectorMatrix, ht, mulVec, dotProduct, transpose_apply,
      Fintype.sum_sum_type, g] using hh
  have hadg : ∀ i j, 0 ≤ a i+d j+∑ k, g i k*y j k := by
    intro i j
    have hh := hw (Sum.inl (i,j))
    simpa [A, vectorMatrix, mulVec, dotProduct, transpose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, a,d,g,add_assoc,mul_comm] using hh
  let φ := dualEnvelope a g
  have hord := horder φ (dualEnvelope_convex a g)
    (fun ht => dualEnvelope_coordMonotone a g (hg ht))
  have hd : ∀ j, φ (y j) ≤ d j := by
    intro j
    unfold φ dualEnvelope
    apply sup'_le
    intro i _
    have h := hadg i j
    linarith
  have ha : ∀ i, -φ (x i) ≤ a i+∑ k, g i k*x i k := by
    intro i
    have h := le_sup' (fun l => -a l-∑ k, g l k*x i k) (mem_univ i)
    change -φ (x i) ≤ _
    dsimp [φ,dualEnvelope] at *
    linarith
  have hsA : -(∑ i, p i*φ (x i)) ≤ ∑ i, p i*(a i+∑ k, g i k*x i k) := by
    calc
      _ = ∑ i, p i*(-φ (x i)) := by simp
      _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (hp i)
  have hsD : (∑ j, q j*φ (y j)) ≤ ∑ j, q j*d j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hd j) (hq j)
  have he : w ⬝ᵥ b = (∑ i, p i*(a i+∑ k, g i k*x i k)) + ∑ j, q j*d j := by
    simp only [dotProduct,b,vectorRhs,Fintype.sum_sum_type,Fintype.sum_prod_type,
      mul_add,sum_add_distrib,mul_sum]
    dsimp [a,d,g]
    have h1 : (∑ i, w (Sum.inl i)*p i) = ∑ i, p i*w (Sum.inl i) := by
      apply sum_congr rfl; intro i _; ring
    have h2 : (∑ i, ∑ k, w (Sum.inr (Sum.inr (i,k)))*(x i k*p i)) =
        ∑ i, ∑ k, p i*(w (Sum.inr (Sum.inr (i,k)))*x i k) := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro k _; ring
    have h3 : (∑ j, w (Sum.inr (Sum.inl j))*q j) = ∑ j, q j*w (Sum.inr (Sum.inl j)) := by
      apply sum_congr rfl; intro j _; ring
    rw [h1,h2,h3]
    ring
  rw [he]
  linarith

lemma finite_vector_transport {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ φ : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ φ →
      (slack = true → ∀ r s, CoordLe r s → φ r ≤ φ s) →
      (∑ i, p i*φ (x i)) ≤ ∑ j, q j*φ (y j)) :
    ∃ (c : ι → κ → ℝ) (s : ι → Fin n → ℝ),
      (∀ i j, 0 ≤ c i j) ∧ (∀ i k, 0 ≤ s i k) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      ∀ i k, (∑ j, c i j*y j k) - (if slack then s i k else 0) = x i k*p i := by
  classical
  obtain ⟨z,hz,hAz⟩ := finite_vector_feasible slack x y p q hp hq horder
  refine ⟨fun i j => z (Sum.inl (i,j)),fun i k => z (Sum.inr (i,k)),
    fun i j => hz _,fun i k => hz _,?_,?_,?_⟩
  · intro i
    have hh := congrFun hAz (Sum.inl i)
    simp [vectorMatrix,vectorRhs,mulVec,dotProduct,Fintype.sum_sum_type,
      Fintype.sum_prod_type] at hh
    rw [sum_comm] at hh
    simpa using hh
  · intro j
    have hh := congrFun hAz (Sum.inr (Sum.inl j))
    simpa [vectorMatrix,vectorRhs,mulVec,dotProduct,Fintype.sum_sum_type,
      Fintype.sum_prod_type,sum_ite_irrel] using hh
  · intro i k
    have hh := congrFun hAz (Sum.inr (Sum.inr (i,k)))
    cases slack <;> simpa [vectorMatrix,vectorRhs,mulVec,dotProduct,Fintype.sum_sum_type,
      Fintype.sum_prod_type,sum_ite_irrel,sub_eq_add_neg,mul_comm] using hh

theorem finite_martingale_matrix {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι]
    (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ φ : (Fin n → ℝ) → ℝ, φ ∈ classCx n →
      (∑ i, p i*φ (x i)) ≤ ∑ j, q j*φ (y j)) :
    ∃ c : ι → κ → ℝ, (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      ∀ i, (∑ j, c i j • y j) = p i • x i := by
  obtain ⟨c,s,hc,hs,hrow,hcol,hmean⟩ := finite_vector_transport false x y p q hp hq
    (fun φ hconv _ => horder φ hconv)
  refine ⟨c,hc,hrow,hcol,?_⟩
  intro i
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hm : (∑ j, c i j*y j k) = x i k*p i := by simpa using hmean i k
  simpa only [mul_comm] using hm

theorem finite_submartingale_matrix {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι]
    (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ φ : (Fin n → ℝ) → ℝ, φ ∈ classIcx n →
      (∑ i, p i*φ (x i)) ≤ ∑ j, q j*φ (y j)) :
    ∃ c : ι → κ → ℝ, (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      ∀ i, CoordLe (p i • x i) (∑ j, c i j • y j) := by
  obtain ⟨c,s,hc,hs,hrow,hcol,hmean⟩ := finite_vector_transport true x y p q hp hq
    (fun φ hconv hmono => horder φ ⟨hmono rfl,hconv⟩)
  refine ⟨c,hc,hrow,hcol,?_⟩
  intro i k
  change p i*x i k ≤ (∑ j, c i j • y j) k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hm : (∑ j, c i j*y j k)-s i k = x i k*p i := by simpa using hmean i k
  nlinarith [hs i k]

end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.finite_vector_feasible
#print axioms MultivariateStrassenFinite.finite_vector_transport
#print axioms MultivariateStrassenFinite.finite_martingale_matrix
#print axioms MultivariateStrassenFinite.finite_submartingale_matrix

set_option autoImplicit false
open scoped BigOperators
open Matrix Finset PalmQueueing.Ordering
namespace MultivariateStrassenFinite
lemma bounded_dual_certificate {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (ε C : ℝ) (hC : 0 ≤ C)
    (w : (ι ⊕ (κ ⊕ (ι × Fin n))) → ℝ)
    (hw : 0 ≤ (vectorMatrix slack y)ᵀ *ᵥ w)
    (hbound : ∀ i k, |w (Sum.inr (Sum.inr (i,k)))| ≤ C)
    (horder : ∀ (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ), 0 ≤ C → (∀ i k, |g i k| ≤ C) →
      (slack = true → ∀ i k, g i k ≤ 0) →
      (∑ i, p i*dualEnvelope a g (x i)) ≤
        (∑ j, q j*dualEnvelope a g (y j)) + C*ε) :
    -C*ε ≤ w ⬝ᵥ vectorRhs x p q := by
  classical
  let A := vectorMatrix (ι := ι) slack y
  let b := vectorRhs x p q
  let a : ι → ℝ := fun i => w (Sum.inl i)
  let d : κ → ℝ := fun j => w (Sum.inr (Sum.inl j))
  let g : ι → Fin n → ℝ := fun i k => w (Sum.inr (Sum.inr (i,k)))
  have hg : slack = true → ∀ i k, g i k ≤ 0 := by
    intro ht i k
    have hh := hw (Sum.inr (i,k))
    simpa [A, vectorMatrix, ht, mulVec, dotProduct, transpose_apply,
      Fintype.sum_sum_type, g] using hh
  have hadg : ∀ i j, 0 ≤ a i+d j+∑ k, g i k*y j k := by
    intro i j
    have hh := hw (Sum.inl (i,j))
    simpa [A, vectorMatrix, mulVec, dotProduct, transpose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, a,d,g,add_assoc,mul_comm] using hh
  let φ := dualEnvelope a g
  have hord := horder a g C hC hbound hg
  have hd : ∀ j, φ (y j) ≤ d j := by
    intro j
    unfold φ dualEnvelope
    apply sup'_le
    intro i _
    have h := hadg i j
    linarith
  have ha : ∀ i, -φ (x i) ≤ a i+∑ k, g i k*x i k := by
    intro i
    have h := le_sup' (fun l => -a l-∑ k, g l k*x i k) (mem_univ i)
    change -φ (x i) ≤ _
    dsimp [φ,dualEnvelope] at *
    linarith
  have hsA : -(∑ i, p i*φ (x i)) ≤ ∑ i, p i*(a i+∑ k, g i k*x i k) := by
    calc
      _ = ∑ i, p i*(-φ (x i)) := by simp
      _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (hp i)
  have hsD : (∑ j, q j*φ (y j)) ≤ ∑ j, q j*d j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hd j) (hq j)
  have he : w ⬝ᵥ b = (∑ i, p i*(a i+∑ k, g i k*x i k)) + ∑ j, q j*d j := by
    simp only [dotProduct,b,vectorRhs,Fintype.sum_sum_type,Fintype.sum_prod_type,
      mul_add,sum_add_distrib,mul_sum]
    dsimp [a,d,g]
    have h1 : (∑ i, w (Sum.inl i)*p i) = ∑ i, p i*w (Sum.inl i) := by
      apply sum_congr rfl; intro i _; ring
    have h2 : (∑ i, ∑ k, w (Sum.inr (Sum.inr (i,k)))*(x i k*p i)) =
        ∑ i, ∑ k, p i*(w (Sum.inr (Sum.inr (i,k)))*x i k) := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro k _; ring
    have h3 : (∑ j, w (Sum.inr (Sum.inl j))*q j) = ∑ j, q j*w (Sum.inr (Sum.inl j)) := by
      apply sum_congr rfl; intro j _; ring
    rw [h1,h2,h3]
    ring
  rw [he]
  linarith

noncomputable def budgetMatrix {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (slack : Bool) (y : κ → Fin n → ℝ) :
    Matrix ((ι ⊕ (κ ⊕ (ι × Fin n))) ⊕ Unit)
      (((ι × κ) ⊕ (ι × Fin n)) ⊕ ((ι × Fin n) ⊕ ((ι × Fin n) ⊕ Unit))) ℝ := by
  classical
  exact fun r c => match r,c with
    | Sum.inl r, Sum.inl c => vectorMatrix slack y r c
    | Sum.inl (Sum.inr (Sum.inr k)), Sum.inr (Sum.inl l) => if k=l then 1 else 0
    | Sum.inl (Sum.inr (Sum.inr k)), Sum.inr (Sum.inr (Sum.inl l)) => if k=l then -1 else 0
    | Sum.inr _, Sum.inr _ => 1
    | _,_ => 0

def budgetRhs {n : ℕ} {ι κ : Type*} (x : ι → Fin n → ℝ) (p : ι → ℝ)
    (q : κ → ℝ) (ε : ℝ) : ((ι ⊕ (κ ⊕ (ι × Fin n))) ⊕ Unit) → ℝ
  | Sum.inl r => vectorRhs x p q r
  | Sum.inr _ => ε

lemma finite_budget_feasible {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (ε : ℝ)
    (horder : ∀ (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ), 0 ≤ C → (∀ i k, |g i k| ≤ C) →
      (slack = true → ∀ i k, g i k ≤ 0) →
      (∑ i, p i*dualEnvelope a g (x i)) ≤
        (∑ j, q j*dualEnvelope a g (y j)) + C*ε) :
    ∃ z, 0 ≤ z ∧ budgetMatrix slack y *ᵥ z = budgetRhs x p q ε := by
  classical
  apply (RiskOrderFarkas.farkas_eq_gen (budgetMatrix slack y) (budgetRhs x p q ε)).mpr
  intro w hw
  let v : (ι ⊕ (κ ⊕ (ι × Fin n))) → ℝ := fun r => w (Sum.inl r)
  let C : ℝ := w (Sum.inr ())
  have hC : 0 ≤ C := by
    have hh := hw (Sum.inr (Sum.inr (Sum.inr ())))
    simpa [budgetMatrix,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,C] using hh
  have hv : 0 ≤ (vectorMatrix slack y)ᵀ *ᵥ v := by
    intro c
    have hh := hw (Sum.inl c)
    simpa [budgetMatrix,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,v] using hh
  have hg : ∀ i k, |v (Sum.inr (Sum.inr (i,k)))| ≤ C := by
    intro i k
    have hp := hw (Sum.inr (Sum.inl (i,k)))
    have hn := hw (Sum.inr (Sum.inr (Sum.inl (i,k))))
    have hplus : 0 ≤ v (Sum.inr (Sum.inr (i,k))) + C := by
      simpa [budgetMatrix,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,v,C] using hp
    have hminus : 0 ≤ -v (Sum.inr (Sum.inr (i,k))) + C := by
      simpa [budgetMatrix,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,v,C] using hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hb := bounded_dual_certificate slack x y p q hp hq ε C hC v hv hg horder
  have he : w ⬝ᵥ budgetRhs x p q ε = v ⬝ᵥ vectorRhs x p q + C*ε := by
    simp only [dotProduct,budgetRhs,Fintype.sum_sum_type,Fintype.sum_unique,v,C]
  rw [he]
  linarith

theorem finite_budget_transport {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (ε : ℝ)
    (horder : ∀ (a : ι → ℝ) (g : ι → Fin n → ℝ) (C : ℝ), 0 ≤ C →
      (∀ i k, |g i k| ≤ C) → (slack = true → ∀ i k, g i k ≤ 0) →
      (∑ i, p i*dualEnvelope a g (x i)) ≤
        (∑ j, q j*dualEnvelope a g (y j)) + C*ε) :
    ∃ (c : ι → κ → ℝ) (s rp rm : ι → Fin n → ℝ),
      (∀ i j, 0 ≤ c i j) ∧ (∀ i k, 0 ≤ s i k) ∧
      (∀ i k, 0 ≤ rp i k) ∧ (∀ i k, 0 ≤ rm i k) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      (∑ i, ∑ k, (rp i k + rm i k)) ≤ ε ∧
      ∀ i k, (∑ j, c i j*y j k) - (if slack then s i k else 0) + rp i k-rm i k = x i k*p i := by
  classical
  obtain ⟨z,hz,hAz⟩ := finite_budget_feasible slack x y p q hp hq ε horder
  let c : ι → κ → ℝ := fun i j => z (Sum.inl (Sum.inl (i,j)))
  let s : ι → Fin n → ℝ := fun i k => z (Sum.inl (Sum.inr (i,k)))
  let rp : ι → Fin n → ℝ := fun i k => z (Sum.inr (Sum.inl (i,k)))
  let rm : ι → Fin n → ℝ := fun i k => z (Sum.inr (Sum.inr (Sum.inl (i,k))))
  refine ⟨c,s,rp,rm,fun i j => hz _,fun i k => hz _,fun i k => hz _,fun i k => hz _,?_,?_,?_,?_⟩
  · intro i
    have hh := congrFun hAz (Sum.inl (Sum.inl i))
    simp [budgetMatrix,budgetRhs,vectorMatrix,vectorRhs,mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type] at hh
    rw [sum_comm] at hh
    simpa [c] using hh
  · intro j
    have hh := congrFun hAz (Sum.inl (Sum.inr (Sum.inl j)))
    simpa [budgetMatrix,budgetRhs,vectorMatrix,vectorRhs,mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type,sum_ite_irrel,c] using hh
  · have hh := congrFun hAz (Sum.inr ())
    have he : (∑ i, ∑ k, rp i k) + (∑ i, ∑ k, rm i k) +
        z (Sum.inr (Sum.inr (Sum.inr ()))) = ε := by
      simpa [budgetMatrix,budgetRhs,mulVec,dotProduct,Fintype.sum_sum_type,
        Fintype.sum_prod_type,rp,rm,add_assoc] using hh
    have hu := hz (Sum.inr (Sum.inr (Sum.inr ())))
    change 0 ≤ z (Sum.inr (Sum.inr (Sum.inr ()))) at hu
    simp only [sum_add_distrib]
    linarith
  · intro i k
    have hh := congrFun hAz (Sum.inl (Sum.inr (Sum.inr (i,k))))
    cases slack <;> simpa [budgetMatrix,budgetRhs,vectorMatrix,vectorRhs,mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type,sum_ite_irrel,c,s,rp,rm,
      sub_eq_add_neg,mul_comm,add_assoc] using hh

end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.bounded_dual_certificate
#print axioms MultivariateStrassenFinite.finite_budget_feasible
#print axioms MultivariateStrassenFinite.finite_budget_transport

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory PalmQueueing.Ordering MultivariateStrassenLaw
namespace MultivariateStrassenFinite
lemma dualEnvelope_continuous {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (g : ι → Fin n → ℝ) : Continuous (dualEnvelope a g) := by
  unfold dualEnvelope
  apply Continuous.finset_sup'_apply
  intro i _
  fun_prop

lemma finite_transport_of_approximations {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι]
    (slack : Bool) (F G : Measure (Fin n → ℝ))
    [IsFiniteMeasure F] [IsFiniteMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (horder : if slack then IcxLe F G else CxLe F G)
    (A B : (Fin n → ℝ) → Fin n → ℝ)
    (hmA : Measurable A) (hmB : Measurable B)
    (hA : Integrable A F) (hB : Integrable B G)
    (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hrepA : F.map A = finiteLaw x p) (hrepB : G.map B = finiteLaw y q) :
    ∃ (c : ι → κ → ℝ) (s rp rm : ι → Fin n → ℝ),
      (∀ i j, 0 ≤ c i j) ∧ (∀ i k, 0 ≤ s i k) ∧
      (∀ i k, 0 ≤ rp i k) ∧ (∀ i k, 0 ≤ rm i k) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      (∑ i, ∑ k, (rp i k + rm i k)) ≤ (n : ℝ)*((∫ z, ‖z-A z‖ ∂F)+(∫ z, ‖z-B z‖ ∂G)) ∧
      ∀ i k, (∑ j, c i j*y j k) - (if slack then s i k else 0) + rp i k-rm i k = x i k*p i := by
  apply finite_budget_transport slack x y p q hp hq
  intro a g C hC hg hsign
  have hm := (dualEnvelope_continuous a g).measurable
  have ha := payoff_of_finite_law F A hmA x p hp hrepA (dualEnvelope a g) hm
  have hb := payoff_of_finite_law G B hmB y q hq hrepB (dualEnvelope a g) hm
  have ho : (∫ z, dualEnvelope a g (A z) ∂F) ≤
      (∫ z, dualEnvelope a g (B z) ∂G) +
      C*(n : ℝ)*((∫ z, ‖z-A z‖ ∂F)+(∫ z, ‖z-B z‖ ∂G)) := by
    cases slack with
    | false => exact cx_dualEnvelope_order_approx F G hF hG horder A B hA hB a g C hC hg
    | true => exact icx_dualEnvelope_order_approx F G hF hG horder A B hA hB a g C hC hg (hsign rfl)
  rw [ha,hb] at ho
  convert ho using 1 <;> ring
end MultivariateStrassenFinite
#print axioms MultivariateStrassenFinite.dualEnvelope_continuous
#print axioms MultivariateStrassenFinite.finite_transport_of_approximations

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory PalmQueueing.Ordering MultivariateStrassenLaw
open MultivariateStrassenFinite MultivariateStrassenPairs MultivariateStrassenDefect
namespace MultivariateStrassenCoupling
lemma approximate_pair_law {n : ℕ} (slack : Bool)
    (F G : Measure (Fin n → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (horder : if slack then IcxLe F G else CxLe F G)
    (A B : (Fin n → ℝ) → Fin n → ℝ)
    (hmA : Measurable A) (hmB : Measurable B)
    (hFA : (Set.range A).Finite) (hFB : (Set.range B).Finite)
    (hA : Integrable A F) (hB : Integrable B G) :
    ∃ μ : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = F.map A ∧ μ.map Prod.snd = G.map B ∧
      ∀ (h : (Fin n → ℝ) → Fin n → ℝ) (M : ℝ), 0 ≤ M →
        (∀ x k, |h x k| ≤ M) → (slack = true → ∀ x k, 0 ≤ h x k) →
        if slack then
          -M*((n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G))) ≤
            ∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂μ
        else
          |∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂μ| ≤
            M*((n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G))) := by
  classical
  obtain ⟨T,hT,hposT,hsumT,hrepA⟩ := finite_range_law F A hmA hFA
  obtain ⟨U,hU,hposU,hsumU,hrepB⟩ := finite_range_law G B hmB hFB
  letI : Nonempty T := hT.to_subtype
  let x : T → Fin n → ℝ := fun i => i.val
  let y : U → Fin n → ℝ := fun j => j.val
  let p : T → ℝ := fun i => ((F.map A) {i.val}).toReal
  let q : U → ℝ := fun j => ((G.map B) {j.val}).toReal
  have hp : ∀ i, 0 ≤ p i := fun _ => ENNReal.toReal_nonneg
  have hq : ∀ j, 0 ≤ q j := fun _ => ENNReal.toReal_nonneg
  have hpsum : ∑ i, p i = 1 := by
    rw [← Finset.sum_coe_sort T (fun a => ((F.map A) {a}).toReal)] at hsumT
    exact hsumT
  obtain ⟨c,s,rp,rm,hc,hs,hrp,hrm,hrow,hcol,hbudget,hmean⟩ :=
    finite_transport_of_approximations slack F G hF hG horder A B hmA hmB hA hB
      x y p q hp hq hrepA hrepB
  obtain ⟨μ,hμ,hμ₁,hμ₂,hformula⟩ := matrix_pair_law x y p q c hc hrow hcol hpsum
  refine ⟨μ,hμ,by rw [hrepA]; exact hμ₁,by rw [hrepB]; exact hμ₂,?_⟩
  intro h M hM hh hsign
  let d : T → Fin n → ℝ := fun i k => (∑ j, c i j*y j k)-x i k*p i
  let e : T → Fin n → ℝ := fun i k => rp i k+rm i k
  have he : ∀ i k, 0 ≤ e i k := fun i k => add_nonneg (hrp i k) (hrm i k)
  have htest : (∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂μ) =
      ∑ i, ∑ k, h (x i) k*d i k := by
    rw [hformula]
    apply sum_congr rfl
    intro i _
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    calc
      (∑ j, c i j*(h (x i) k*(y j k-x i k))) =
          ∑ j, (h (x i) k*(c i j*y j k)-(h (x i) k*x i k)*c i j) := by
        apply sum_congr rfl; intro j _; ring
      _ = h (x i) k*d i k := by rw [sum_sub_distrib,← mul_sum,← mul_sum,hrow]; dsimp [d]; ring
  rw [htest]
  cases slack with
  | false =>
    have hd : ∀ i k, |d i k| ≤ e i k := by
      intro i k
      have hm := hmean i k
      simp only [Bool.false_eq_true,↓reduceIte] at hm
      dsimp only [d,e]
      exact abs_le.mpr ⟨by linarith [hrp i k,hrm i k],by linarith [hrp i k,hrm i k]⟩
    exact weighted_error_bound d e (fun i k => h (x i) k) M _ hM he hd
      (fun i k => hh (x i) k) hbudget
  | true =>
    have hd : ∀ i k, -e i k ≤ d i k := by
      intro i k
      have hm := hmean i k
      simp only [↓reduceIte] at hm
      dsimp only [d,e]
      linarith [hs i k,hrm i k]
    exact weighted_error_lower d e (fun i k => h (x i) k) M _ hM he hd
      (fun i k => hsign rfl (x i) k) (fun i k => le_trans (le_abs_self _) (hh (x i) k)) hbudget
lemma exists_approximate_pair_law {n : ℕ} (slack : Bool)
    (F G : Measure (Fin n → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (horder : if slack then IcxLe F G else CxLe F G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (A B : (Fin n → ℝ) → Fin n → ℝ)
      (μ : Measure ((Fin n → ℝ) × (Fin n → ℝ))),
      Measurable A ∧ Measurable B ∧ (Set.range A).Finite ∧ (Set.range B).Finite ∧
      Integrable A F ∧ Integrable B G ∧
      (∫ x, ‖x-A x‖ ∂F) < ε ∧ (∫ y, ‖y-B y‖ ∂G) < ε ∧
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = F.map A ∧ μ.map Prod.snd = G.map B ∧
      ∀ (h : (Fin n → ℝ) → Fin n → ℝ) (M : ℝ), 0 ≤ M →
        (∀ x k, |h x k| ≤ M) → (slack = true → ∀ x k, 0 ≤ h x k) →
        if slack then -M*ε ≤ ∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂μ
        else |∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂μ| ≤ M*ε := by
  let δ : ℝ := ε/(2*((n : ℝ)+1))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 2*((n : ℝ)+1) := by positivity
  have hδ : 0 < δ := div_pos hε hd
  have hδeq : 2*((n : ℝ)+1)*δ = ε := by
    dsimp [δ]
    field_simp
  have hδε : δ ≤ ε := by nlinarith
  obtain ⟨A,hmA,hFA,hA,heA⟩ := MultivariateStrassenApproximation.exists_identity_finite_L1 F hF δ hδ
  obtain ⟨B,hmB,hFB,hB,heB⟩ := MultivariateStrassenApproximation.exists_identity_finite_L1 G hG δ hδ
  obtain ⟨μ,hμ,hμA,hμB,htest⟩ := approximate_pair_law slack F G hF hG horder
    A B hmA hmB hFA hFB hA hB
  have hb : (n : ℝ)*((∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G)) ≤ ε := by
    have hh : (∫ x, ‖x-A x‖ ∂F)+(∫ y, ‖y-B y‖ ∂G) ≤ 2*δ := by linarith
    have hh₁ := mul_le_mul_of_nonneg_left hh hn
    nlinarith
  refine ⟨A,B,μ,hmA,hmB,hFA,hFB,hA,hB,lt_of_lt_of_le heA hδε,
    lt_of_lt_of_le heB hδε,hμ,hμA,hμB,?_⟩
  intro h M hM hh hsign
  have ht := htest h M hM hh hsign
  have hMb := mul_le_mul_of_nonneg_left hb hM
  cases slack <;> simp only [Bool.false_eq_true,↓reduceIte] at ht ⊢ <;> linarith

end MultivariateStrassenCoupling
#print axioms MultivariateStrassenCoupling.approximate_pair_law

#print axioms MultivariateStrassenCoupling.exists_approximate_pair_law

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
open PalmQueueing.Ordering MultivariateStrassenCompactness MultivariateStrassenApproximation
namespace MultivariateStrassenCoupling
lemma exists_approximate_couplings_with_exact_marginal_limit {d : ℕ} (slack : Bool)
    (F G : Measure (Fin d → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (horder : if slack then IcxLe F G else CxLe F G) :
    ∃ A B : ℕ → (Fin d → ℝ) → Fin d → ℝ,
    ∃ μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
    ∃ ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)), ∃ φ : ℕ → ℕ,
      (∀ m, Measurable (A m) ∧ Measurable (B m) ∧
        (Set.range (A m)).Finite ∧ (Set.range (B m)).Finite ∧
        Integrable (A m) F ∧ Integrable (B m) G ∧
        (∫ x, ‖x-A m x‖ ∂F) < 1/((m : ℝ)+1) ∧
        (∫ y, ‖y-B m y‖ ∂G) < 1/((m : ℝ)+1) ∧
        (μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map (A m) ∧
        (μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map (B m) ∧
        ∀ (h : (Fin d → ℝ) → Fin d → ℝ) (M : ℝ), 0 ≤ M →
          (∀ x k, |h x k| ≤ M) → (slack = true → ∀ x k, 0 ≤ h x k) →
          if slack then -M*(1/((m : ℝ)+1)) ≤
            ∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂(μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
          else |∫ z, ∑ k, h z.1 k*(z.2 k-z.1 k) ∂(μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ)))| ≤
            M*(1/((m : ℝ)+1))) ∧
      Tendsto (fun m => ∫ x, ‖x-A m x‖ ∂F) atTop (𝓝 0) ∧
      Tendsto (fun m => ∫ y, ‖y-B m y‖ ∂G) atTop (𝓝 0) ∧
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F ∧
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G := by
  classical
  choose A B μ hmA hmB hFA hFB hiA hiB heA heB hμ hfst hsnd ht using
    (fun m : ℕ => exists_approximate_pair_law slack F G hF hG horder (1/((m : ℝ)+1)) (by positivity))
  let γ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) := fun m => ⟨μ m,hμ m⟩
  let C := (∫ x, ‖x‖ ∂F)+(∫ y, ‖y‖ ∂G)+2
  have hC : 0 ≤ C := by
    have h₁ : 0 ≤ ∫ x, ‖x‖ ∂F := integral_nonneg (fun x => norm_nonneg x)
    have h₂ : 0 ≤ ∫ y, ‖y‖ ∂G := integral_nonneg (fun y => norm_nonneg y)
    dsimp only [C]; linarith
  have hb : ∀ m, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖)
      (γ m : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ∧
      (∫ z, ‖z‖ ∂(γ m : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C := by
    intro m
    have hf : IdentDistrib Prod.fst (A m) (μ m) F :=
      ⟨measurable_fst.aemeasurable,(hmA m).aemeasurable,hfst m⟩
    have hs : IdentDistrib Prod.snd (B m) (μ m) G :=
      ⟨measurable_snd.aemeasurable,(hmB m).aemeasurable,hsnd m⟩
    have hε : (1 : ℝ)/((m : ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hh := pair_moment_bound F G (fun x => x) (A m) (fun y => y) (B m)
      (integrable_identity F hF) (integrable_identity G hG) (hiA m) (hiB m)
      (μ m) hf hs _ (heA m).le (heB m).le
    refine ⟨hh.1,hh.2.trans ?_⟩
    dsimp only [C]; linarith
  obtain ⟨ν,φ,hφ,hlim⟩ := subsequence_of_bounded_first_moment γ C hC
    (fun m => (hb m).1) (fun m => (hb m).2)
  have heAX : Tendsto (fun m => ∫ x, ‖x-A m x‖ ∂F) atTop (𝓝 0) :=
    squeeze_zero (fun m => integral_nonneg (fun _ => norm_nonneg _))
      (fun m => (heA m).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have heBY : Tendsto (fun m => ∫ y, ‖y-B m y‖ ∂G) atTop (𝓝 0) :=
    squeeze_zero (fun m => integral_nonneg (fun _ => norm_nonneg _))
      (fun m => (heB m).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨A,B,γ,ν,φ,?_,heAX,heBY,hφ,hlim,?_,?_⟩
  · intro m
    exact ⟨hmA m,hmB m,hFA m,hFB m,hiA m,hiB m,heA m,heB m,hfst m,hsnd m,ht m⟩
  · have hh := marginal_of_L1_weak_limit F (fun x => x) A
      (integrable_identity F hF) hiA heAX γ ν φ hφ hlim Prod.fst continuous_fst hfst
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map id at hh
    rw [Measure.map_id] at hh
    exact hh
  · have hh := marginal_of_L1_weak_limit G (fun y => y) B
      (integrable_identity G hG) hiB heBY γ ν φ hφ hlim Prod.snd continuous_snd hsnd
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map id at hh
    rw [Measure.map_id] at hh
    exact hh
end MultivariateStrassenCoupling
#print axioms MultivariateStrassenCoupling.exists_approximate_couplings_with_exact_marginal_limit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped BigOperators Topology NNReal ENNReal
/- Vector norm-tail adaptation of the accepted scalar RiskOrderCompactness helpers. -/
namespace MultivariateStrassenCompactness
lemma full_uniform_integrability_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, ‖X ω - A n ω‖ ∂P) ≤ 1) :
    UniformIntegrable A 1 P := by
  let C := (∫ ω, ‖X ω‖ ∂P) + 1
  have hC : 0 ≤ C := by
    have hn : 0 ≤ ∫ ω, ‖X ω‖ ∂P := integral_nonneg (fun ω => norm_nonneg _)
    dsimp only [C]; linarith
  let c : ℝ≥0 := ⟨C, hC⟩
  refine ⟨fun n => (hA n).aestronglyMeasurable, uniform_integrability_of_L1 P X A hX hA he,
    ⟨c, ?_⟩⟩
  intro n
  have hn : eLpNorm (A n) 1 P = ENNReal.ofReal (∫ ω, ‖A n ω‖ ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hA n)]
  rw [hn]
  have hbound : (∫ ω, ‖A n ω‖ ∂P) ≤ C :=
    integral_norm_le_of_L1_close P X (A n) hX (hA n) 1 (hb n)
  calc
    ENNReal.ofReal (∫ ω, ‖A n ω‖ ∂P) ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbound
    _ = (c : ℝ≥0∞) := by rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hC]; rfl

lemma uniform_norm_tails_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, ‖X ω - A n ω‖ ∂P) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      (∫ ω in {ω | (C : ℝ) ≤ ‖A n ω‖}, ‖A n ω‖ ∂P) ≤ ε := by
  have hu := full_uniform_integrability_of_L1 P X A hX hA he hb
  obtain ⟨C, hC⟩ := hu.spec (by norm_num) (by norm_num) hε
  refine ⟨C, fun n => ?_⟩
  let s : Set Ω := {ω | C ≤ ‖A n ω‖₊}
  have hs : NullMeasurableSet s P :=
    ((hA n).aemeasurable.nnnorm.nullMeasurable measurableSet_Ici)
  have hi : Integrable (s.indicator (A n)) P := (hA n).indicator₀ hs
  have hn : eLpNorm (s.indicator (A n)) 1 P =
      ENNReal.ofReal (∫ ω in {ω | (C : ℝ) ≤ ‖A n ω‖}, ‖A n ω‖ ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    rw [← integral_indicator₀]
    · apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        simp only [s, Set.indicator, Set.mem_ofPred_eq]
        split_ifs <;> simp_all [← NNReal.coe_le_coe])
    · convert hs using 1
      ext ω
      simp only [s, Set.mem_ofPred_eq, ← NNReal.coe_le_coe, coe_nnnorm]
  have h := hC n
  change eLpNorm (s.indicator (A n)) 1 P ≤ _ at h
  rw [hn] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

lemma norm_tail_integral_eq_of_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω') (f : Ω → Fin d → ℝ) (g : Ω' → Fin d → ℝ)
    (hf : Measurable f) (hg : Measurable g) (h : IdentDistrib f g P Q) (C : ℝ) :
    (∫ ω in {ω | C ≤ ‖f ω‖}, ‖f ω‖ ∂P) =
      ∫ ω in {ω | C ≤ ‖g ω‖}, ‖g ω‖ ∂Q := by
  have hsf : MeasurableSet {ω | C ≤ ‖f ω‖} := measurableSet_le measurable_const hf.norm
  have hsg : MeasurableSet {ω | C ≤ ‖g ω‖} := measurableSet_le measurable_const hg.norm
  rw [← integral_indicator hsf, ← integral_indicator hsg]
  have hd := ((h.comp measurable_norm).comp (measurable_id.indicator (measurableSet_Ici (a := C)))).integral_eq
  simpa only [Function.comp_def, Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq, id_eq] using hd

lemma uniform_law_norm_tails_of_L1 {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P) (hmA : ∀ n, Measurable (A n))
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, ‖X ω - A n ω‖ ∂P) ≤ 1)
    (μ : ℕ → Measure Ω') (f : Ω' → Fin d → ℝ) (hf : Measurable f)
    (hmap : ∀ n, (μ n).map f = P.map (A n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      (∫ z in {z | (C : ℝ) ≤ ‖f z‖}, ‖f z‖ ∂μ n) ≤ ε := by
  obtain ⟨C, hC⟩ := uniform_norm_tails_of_L1 P X A hX hA he hb ε hε
  refine ⟨C, fun n => ?_⟩
  have hd : IdentDistrib f (A n) (μ n) P :=
    ⟨hf.aemeasurable, (hmA n).aemeasurable, hmap n⟩
  rw [norm_tail_integral_eq_of_identDistrib (μ n) P f (A n) hf (hmA n) hd]
  exact hC n

end MultivariateStrassenCompactness
#print axioms MultivariateStrassenCompactness.full_uniform_integrability_of_L1
#print axioms MultivariateStrassenCompactness.uniform_norm_tails_of_L1
#print axioms MultivariateStrassenCompactness.norm_tail_integral_eq_of_identDistrib
#print axioms MultivariateStrassenCompactness.uniform_law_norm_tails_of_L1

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators Topology BoundedContinuousFunction
/- Pure scalar clipping helpers are unchanged from the accepted scalar Strassen source.
   Tests below depend on a vector source and a selected vector coordinate. -/
namespace MultivariateStrassenLimit
def clip (C x : ℝ) : ℝ := max (-C) (min C x)

lemma continuous_clip (C : ℝ) : Continuous (clip C) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma abs_clip_le (C : ℝ) (hC : 0 ≤ C) (x : ℝ) : |clip C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma abs_sub_clip_le_abs (C : ℝ) (hC : 0 ≤ C) (x : ℝ) : |x - clip C x| ≤ |x| := by
  by_cases hx : x ≤ -C
  · have hxC : x ≤ C := by linarith
    rw [clip, min_eq_right hxC, max_eq_left hx, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · by_cases hxC : C ≤ x
    · rw [clip, min_eq_left hxC, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [clip, min_eq_right (le_of_not_ge hxC), max_eq_right (le_of_not_ge hx), sub_self, abs_zero]
      exact abs_nonneg _

lemma clip_eq_of_abs_lt (C x : ℝ) (hx : |x| < C) : clip C x = x := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hx
  rw [clip, min_eq_right hr.le, max_eq_right hl.le]

lemma abs_sub_clip_le_tail (C : ℝ) (hC : 0 ≤ C) (x : ℝ) :
    |x - clip C x| ≤ {r : ℝ | C ≤ |r|}.indicator (fun r => |r|) x := by
  by_cases hx : C ≤ |x|
  · rw [indicator_of_mem (show x ∈ {r : ℝ | C ≤ |r|} from hx)]
    exact abs_sub_clip_le_abs C hC x
  · rw [indicator_of_notMem (show x ∉ {r : ℝ | C ≤ |r|} from hx), clip_eq_of_abs_lt C x (lt_of_not_ge hx), sub_self, abs_zero]

noncomputable def clippedTest {d : ℕ} (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d)
    (C : ℝ) (hC : 0 ≤ C) : ((Fin d → ℝ) × (Fin d → ℝ)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ψ z.1*(clip C (z.2 k)-clip C (z.1 k)))
    ((ψ.continuous.comp continuous_fst).mul
      (((continuous_clip C).comp ((continuous_apply k).comp continuous_snd)).sub
        ((continuous_clip C).comp ((continuous_apply k).comp continuous_fst))))
    (‖ψ‖*(2*C)) (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      have hp : |ψ z.1| ≤ ‖ψ‖ := by simpa only [Real.norm_eq_abs] using ψ.norm_coe_le_norm z.1
      have hd : |clip C (z.2 k)-clip C (z.1 k)| ≤ 2*C :=
        (abs_sub _ _).trans (by linarith [abs_clip_le C hC (z.2 k),abs_clip_le C hC (z.1 k)])
      exact mul_le_mul hp hd (abs_nonneg _) (norm_nonneg _))

lemma abs_coord_sub_clip_le_norm_tail {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    (x : Fin d → ℝ) (k : Fin d) :
    |x k-clip C (x k)| ≤ {x : Fin d → ℝ | C ≤ ‖x‖}.indicator (fun x => ‖x‖) x := by
  have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
  by_cases hx : C ≤ ‖x‖
  · rw [indicator_of_mem (show x ∈ {x : Fin d → ℝ | C ≤ ‖x‖} from hx)]
    exact (abs_sub_clip_le_abs C hC (x k)).trans hk
  · rw [indicator_of_notMem (show x ∉ {x : Fin d → ℝ | C ≤ ‖x‖} from hx),
      clip_eq_of_abs_lt C (x k) (lt_of_le_of_lt hk (lt_of_not_ge hx)),sub_self,abs_zero]

lemma test_clipping_error {d : ℕ} (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d)
    (C : ℝ) (hC : 0 ≤ C) (z : (Fin d → ℝ) × (Fin d → ℝ)) :
    |ψ z.1*(z.2 k-z.1 k)-clippedTest ψ k C hC z| ≤
      ‖ψ‖*(|z.2 k-clip C (z.2 k)|+|z.1 k-clip C (z.1 k)|) := by
  change |ψ z.1*(z.2 k-z.1 k)-ψ z.1*(clip C (z.2 k)-clip C (z.1 k))| ≤ _
  rw [← mul_sub,abs_mul]
  have he : (z.2 k-z.1 k)-(clip C (z.2 k)-clip C (z.1 k)) =
      (z.2 k-clip C (z.2 k))-(z.1 k-clip C (z.1 k)) := by ring
  rw [he]
  have hp : |ψ z.1| ≤ ‖ψ‖ := by simpa only [Real.norm_eq_abs] using ψ.norm_coe_le_norm z.1
  exact mul_le_mul hp (abs_sub _ _) (abs_nonneg _) (norm_nonneg _)

lemma integrable_test {d : ℕ} (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d)
    (hf : Integrable Prod.fst μ) (hs : Integrable Prod.snd μ) :
    Integrable (fun z => ψ z.1*(z.2 k-z.1 k)) μ :=
  ((hs.eval k).sub (hf.eval k)).bdd_mul (ψ.continuous.comp continuous_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => ψ.norm_coe_le_norm z.1))

lemma integral_test_clipping_error {d : ℕ} (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    [IsFiniteMeasure μ] (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d) (C : ℝ) (hC : 0 ≤ C)
    (hf : Integrable Prod.fst μ) (hs : Integrable Prod.snd μ) :
    |(∫ z, ψ z.1*(z.2 k-z.1 k) ∂μ)-(∫ z, clippedTest ψ k C hC z ∂μ)| ≤
      ‖ψ‖*((∫ z in {z | C ≤ ‖z.1‖}, ‖z.1‖ ∂μ)+(∫ z in {z | C ≤ ‖z.2‖}, ‖z.2‖ ∂μ)) := by
  let F : Set ((Fin d → ℝ) × (Fin d → ℝ)) := {z | C ≤ ‖z.1‖}
  let S : Set ((Fin d → ℝ) × (Fin d → ℝ)) := {z | C ≤ ‖z.2‖}
  have hF : MeasurableSet F := measurableSet_le measurable_const measurable_fst.norm
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_snd.norm
  have hiF : Integrable (F.indicator (fun z => ‖z.1‖)) μ := hf.norm.indicator hF
  have hiS : Integrable (S.indicator (fun z => ‖z.2‖)) μ := hs.norm.indicator hS
  have hiT := integrable_test μ ψ k hf hs
  have hiC : Integrable (clippedTest ψ k C hC) μ := (clippedTest ψ k C hC).integrable μ
  have hb : ∀ z : (Fin d → ℝ) × (Fin d → ℝ),
      |ψ z.1*(z.2 k-z.1 k)-clippedTest ψ k C hC z| ≤
      ‖ψ‖*(F.indicator (fun z => ‖z.1‖) z+S.indicator (fun z => ‖z.2‖) z) := by
    intro z
    have h₁ := abs_coord_sub_clip_le_norm_tail C hC z.1 k
    have h₂ := abs_coord_sub_clip_le_norm_tail C hC z.2 k
    have he₁ : {x : Fin d → ℝ | C ≤ ‖x‖}.indicator (fun x => ‖x‖) z.1 =
        F.indicator (fun z => ‖z.1‖) z := by simp only [F,indicator,mem_ofPred_eq]
    have he₂ : {x : Fin d → ℝ | C ≤ ‖x‖}.indicator (fun x => ‖x‖) z.2 =
        S.indicator (fun z => ‖z.2‖) z := by simp only [S,indicator,mem_ofPred_eq]
    rw [he₁] at h₁
    rw [he₂] at h₂
    exact (test_clipping_error ψ k C hC z).trans
      (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
  rw [← integral_sub hiT hiC]
  calc
    _ ≤ ∫ z, |ψ z.1*(z.2 k-z.1 k)-clippedTest ψ k C hC z| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => ψ z.1*(z.2 k-z.1 k)-clippedTest ψ k C hC z)
    _ ≤ ∫ z, ‖ψ‖*(F.indicator (fun z => ‖z.1‖) z+S.indicator (fun z => ‖z.2‖) z) ∂μ :=
      integral_mono (hiT.sub hiC).abs ((hiF.add hiS).const_mul ‖ψ‖) hb
    _ = _ := by rw [integral_const_mul,integral_add hiF hiS,integral_indicator hF,integral_indicator hS]
end MultivariateStrassenLimit
#print axioms MultivariateStrassenLimit.continuous_clip
#print axioms MultivariateStrassenLimit.abs_clip_le
#print axioms MultivariateStrassenLimit.abs_sub_clip_le_abs
#print axioms MultivariateStrassenLimit.clip_eq_of_abs_lt
#print axioms MultivariateStrassenLimit.abs_sub_clip_le_tail
#print axioms MultivariateStrassenLimit.abs_coord_sub_clip_le_norm_tail
#print axioms MultivariateStrassenLimit.test_clipping_error
#print axioms MultivariateStrassenLimit.integrable_test
#print axioms MultivariateStrassenLimit.integral_test_clipping_error

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal BoundedContinuousFunction
/- Coordinate mean-test convergence, adapted from the accepted scalar Strassen proof.
   Uniform tail bounds use vector norms and the two marginal approximations may live
   on different probability spaces. -/
namespace MultivariateStrassenLimit
lemma tendsto_test_integral_of_uniform_tails {d : ℕ}
    (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) (ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hf : ∀ n, Integrable Prod.fst (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hs : ∀ n, Integrable Prod.snd (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hvf : Integrable Prod.fst (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hvs : Integrable Prod.snd (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ((∫ z in {z : (Fin d → ℝ) × (Fin d → ℝ) | C ≤ ‖z.1‖}, ‖z.1‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) +
        ∫ z in {z : (Fin d → ℝ) × (Fin d → ℝ) | C ≤ ‖z.2‖}, ‖z.2‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ ε) ∧
      ((∫ z in {z : (Fin d → ℝ) × (Fin d → ℝ) | C ≤ ‖z.1‖}, ‖z.1‖ ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) +
        ∫ z in {z : (Fin d → ℝ) × (Fin d → ℝ) | C ≤ ‖z.2‖}, ‖z.2‖ ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ ε)
    (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d) :
    Tendsto (fun n => ∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) atTop
      (𝓝 (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (4 * (‖ψ‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : 4 * (‖ψ‖ + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  obtain ⟨C, hC, htμ, htν⟩ := htail δ hδ
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (clippedTest ψ k C hC)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := (integral_test_clipping_error (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ψ k C hC (hf n) (hs n)).trans
    (mul_le_mul_of_nonneg_left (htμ n) (norm_nonneg _))
  have h2 := (integral_test_clipping_error (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ψ k C hC hvf hvs).trans
    (mul_le_mul_of_nonneg_left htν (norm_nonneg _))
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have ha := abs_sub_le
    (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (∫ z, clippedTest ψ k C hC z ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
  have hb := abs_sub_le
    (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (∫ z, clippedTest ψ k C hC z ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (∫ z, clippedTest ψ k C hC z ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
  rw [abs_sub_comm (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))] at h2
  nlinarith

lemma norm_tail_antitone {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Ω → Fin d → ℝ) (hf : Integrable f P) (a b : ℝ) (hab : a ≤ b) :
    (∫ ω in {ω | b ≤ ‖f ω‖}, ‖f ω‖ ∂P) ≤ ∫ ω in {ω | a ≤ ‖f ω‖}, ‖f ω‖ ∂P := by
  apply setIntegral_mono_set hf.norm.integrableOn (ae_of_all _ (fun ω => norm_nonneg _))
  exact ae_of_all _ (fun ω hω => hab.trans hω)

lemma norm_tails_of_integrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Ω → Fin d → ℝ) (hf : Integrable f P) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, (∫ ω in {ω | (C : ℝ) ≤ ‖f ω‖}, ‖f ω‖ ∂P) ≤ ε := by
  have he : Tendsto (fun _ : ℕ => ∫ ω, ‖f ω - f ω‖ ∂P) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨C, hC⟩ := MultivariateStrassenCompactness.uniform_norm_tails_of_L1 P f (fun _ => f) hf
    (fun _ => hf) he (fun _ => by simp) ε hε
  exact ⟨C, hC 0⟩

lemma tendsto_test_integral_of_L1_marginals {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω') (X : Ω → Fin d → ℝ) (Y : Ω' → Fin d → ℝ)
    (A : ℕ → Ω → Fin d → ℝ) (B : ℕ → Ω' → Fin d → ℝ)
    (hX : Integrable X P) (hY : Integrable Y Q)
    (hA : ∀ n, Integrable (A n) P) (hB : ∀ n, Integrable (B n) Q)
    (hmA : ∀ n, Measurable (A n)) (hmB : ∀ n, Measurable (B n))
    (heA : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (heB : Tendsto (fun n => ∫ ω, ‖Y ω - B n ω‖ ∂Q) atTop (𝓝 0))
    (hbA : ∀ n, (∫ ω, ‖X ω - A n ω‖ ∂P) ≤ 1)
    (hbB : ∀ n, (∫ ω, ‖Y ω - B n ω‖ ∂Q) ≤ 1)
    (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) (ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hfst : ∀ n, (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = P.map (A n))
    (hsnd : ∀ n, (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = Q.map (B n))
    (hvfst : (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = P.map X)
    (hvsnd : (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = Q.map Y)
    (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d) :
    Tendsto (fun n => ∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) atTop
      (𝓝 (∫ z, ψ z.1 * (z.2 k - z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))) := by
  have hif : ∀ n, Integrable Prod.fst (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    intro n
    have hd : ProbabilityTheory.IdentDistrib Prod.fst (A n) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) P :=
      ⟨measurable_fst.aemeasurable, (hmA n).aemeasurable, hfst n⟩
    exact hd.integrable_iff.mpr (hA n)
  have his : ∀ n, Integrable Prod.snd (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) := by
    intro n
    have hd : ProbabilityTheory.IdentDistrib Prod.snd (B n) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Q :=
      ⟨measurable_snd.aemeasurable, (hmB n).aemeasurable, hsnd n⟩
    exact hd.integrable_iff.mpr (hB n)
  have hdf : ProbabilityTheory.IdentDistrib Prod.fst X (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) P :=
    ⟨measurable_fst.aemeasurable, hX.aemeasurable, hvfst⟩
  have hds : ProbabilityTheory.IdentDistrib Prod.snd Y (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Q :=
    ⟨measurable_snd.aemeasurable, hY.aemeasurable, hvsnd⟩
  have hvf := hdf.integrable_iff.mpr hX
  have hvs := hds.integrable_iff.mpr hY
  apply tendsto_test_integral_of_uniform_tails μ ν hweak hif his hvf hvs ?_ ψ k
  intro ε hε
  obtain ⟨CA, hCA⟩ := MultivariateStrassenCompactness.uniform_law_norm_tails_of_L1 P X A hX hA hmA
    heA hbA (fun n => (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) Prod.fst measurable_fst hfst (ε / 2) (half_pos hε)
  obtain ⟨CB, hCB⟩ := MultivariateStrassenCompactness.uniform_law_norm_tails_of_L1 Q Y B hY hB hmB
    heB hbB (fun n => (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) Prod.snd measurable_snd hsnd (ε / 2) (half_pos hε)
  obtain ⟨CF, hCF⟩ := norm_tails_of_integrable (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.fst hvf (ε / 2) (half_pos hε)
  obtain ⟨CS, hCS⟩ := norm_tails_of_integrable (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.snd hvs (ε / 2) (half_pos hε)
  let C : ℝ := max (max (CA : ℝ) (CB : ℝ)) (max (CF : ℝ) (CS : ℝ))
  have hAC : (CA : ℝ) ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : (CB : ℝ) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hFC : (CF : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hSC : (CS : ℝ) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, CA.coe_nonneg.trans hAC, ?_, ?_⟩
  · intro n
    have ha := (norm_tail_antitone (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.fst (hif n) _ _ hAC).trans (hCA n)
    have hb := (norm_tail_antitone (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.snd (his n) _ _ hBC).trans (hCB n)
    linarith
  · have ha := (norm_tail_antitone (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.fst hvf _ _ hFC).trans hCF
    have hb := (norm_tail_antitone (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) Prod.snd hvs _ _ hSC).trans hCS
    linarith

end MultivariateStrassenLimit
#print axioms MultivariateStrassenLimit.tendsto_test_integral_of_uniform_tails
#print axioms MultivariateStrassenLimit.norm_tail_antitone
#print axioms MultivariateStrassenLimit.norm_tails_of_integrable
#print axioms MultivariateStrassenLimit.tendsto_test_integral_of_L1_marginals

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology BoundedContinuousFunction
open PalmQueueing.Ordering MultivariateStrassenApproximation MultivariateStrassenCoupling
namespace MultivariateStrassenLimit
lemma exists_coupling_law_continuous_tests {d : ℕ} (slack : Bool)
    (F G : Measure (Fin d → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (horder : if slack then IcxLe F G else CxLe F G) :
    ∃ ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F ∧
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G ∧
      ∀ (ψ : (Fin d → ℝ) →ᵇ ℝ) (k : Fin d), (slack = true → ∀ x, 0 ≤ ψ x) →
        if slack then 0 ≤ ∫ z, ψ z.1*(z.2 k-z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
        else (∫ z, ψ z.1*(z.2 k-z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) = 0 := by
  classical
  obtain ⟨A,B,μ,ν,φ,hdata,heA,heB,hφ,hweak,hvf,hvs⟩ :=
    exists_approximate_couplings_with_exact_marginal_limit slack F G hF hG horder
  have hmA : ∀ m, Measurable (A m) := fun m => (hdata m).1
  have hmB : ∀ m, Measurable (B m) := fun m => (hdata m).2.1
  have hiA : ∀ m, Integrable (A m) F := fun m => (hdata m).2.2.2.2.1
  have hiB : ∀ m, Integrable (B m) G := fun m => (hdata m).2.2.2.2.2.1
  have hfst : ∀ m, (μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map (A m) :=
    fun m => (hdata m).2.2.2.2.2.2.2.2.1
  have hsnd : ∀ m, (μ m : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map (B m) :=
    fun m => (hdata m).2.2.2.2.2.2.2.2.2.1
  have hε : ∀ m : ℕ, (1 : ℝ)/((m : ℝ)+1) ≤ 1 := by
    intro m
    apply (div_le_iff₀ (by positivity)).mpr
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbA : ∀ m, (∫ x, ‖x-A m x‖ ∂F) ≤ 1 :=
    fun m => ((hdata m).2.2.2.2.2.2.1).le.trans (hε m)
  have hbB : ∀ m, (∫ y, ‖y-B m y‖ ∂G) ≤ 1 :=
    fun m => ((hdata m).2.2.2.2.2.2.2.1).le.trans (hε m)
  have hvf' : (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map (fun x => x) := by
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map id
    rw [Measure.map_id]; exact hvf
  have hvs' : (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map (fun y => y) := by
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map id
    rw [Measure.map_id]; exact hvs
  refine ⟨ν,hvf,hvs,?_⟩
  intro ψ k hψ
  have hlim := tendsto_test_integral_of_L1_marginals F G (fun x => x) (fun y => y)
    (A ∘ φ) (B ∘ φ) (integrable_identity F hF) (integrable_identity G hG)
    (fun m => hiA (φ m)) (fun m => hiB (φ m)) (fun m => hmA (φ m)) (fun m => hmB (φ m))
    (heA.comp hφ.tendsto_atTop) (heB.comp hφ.tendsto_atTop)
    (fun m => hbA (φ m)) (fun m => hbB (φ m)) (μ ∘ φ) ν hweak
    (fun m => hfst (φ m)) (fun m => hsnd (φ m)) hvf' hvs' ψ k
  let h : (Fin d → ℝ) → Fin d → ℝ := fun x j => if j=k then ψ x else 0
  have hh : ∀ x j, |h x j| ≤ ‖ψ‖ := by
    intro x j
    by_cases hj : j=k
    · simp only [h,hj,↓reduceIte]
      simpa only [Real.norm_eq_abs] using ψ.norm_coe_le_norm x
    · simp only [h,hj,↓reduceIte,abs_zero]
      exact norm_nonneg _
  have hs : slack = true → ∀ x j, 0 ≤ h x j := by
    intro ht x j
    dsimp only [h]
    split_ifs
    · exact hψ ht x
    · rfl
  have hbound : ∀ m, if slack then
      -‖ψ‖*(1/((φ m : ℝ)+1)) ≤ ∫ z, ψ z.1*(z.2 k-z.1 k) ∂(μ (φ m) : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    else |∫ z, ψ z.1*(z.2 k-z.1 k) ∂(μ (φ m) : Measure ((Fin d → ℝ) × (Fin d → ℝ)))| ≤
      ‖ψ‖*(1/((φ m : ℝ)+1)) := by
    intro m
    have ht := (hdata (φ m)).2.2.2.2.2.2.2.2.2.2 h ‖ψ‖ (norm_nonneg _) hh hs
    simpa only [h,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] using ht
  have hzero : Tendsto (fun m => ‖ψ‖*(1/((φ m : ℝ)+1))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖ψ‖) atTop (𝓝 ‖ψ‖)).mul (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop))
  cases slack with
  | false =>
    have hle : |∫ z, ψ z.1*(z.2 k-z.1 k) ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))| ≤ 0 :=
      le_of_tendsto_of_tendsto' hlim.abs hzero hbound
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  | true =>
    have hn : Tendsto (fun m => -‖ψ‖*(1/((φ m : ℝ)+1))) atTop (𝓝 0) := by
      simpa only [neg_mul,neg_zero] using hzero.neg
    exact le_of_tendsto_of_tendsto' hn hlim hbound
end MultivariateStrassenLimit
#print axioms MultivariateStrassenLimit.exists_coupling_law_continuous_tests

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
open PalmQueueing.Ordering MultivariateStrassenApproximation
open MultivariateStrassenLimit MultivariateStrassenBorel MultivariateStrassenConditionalMean
namespace MultivariateStrassenForward
lemma cx_implies_martingale {d : ℕ}
    (F G : Measure (Fin d → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G) (horder : CxLe F G) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : Ω → Fin d → ℝ), Measurable X ∧ Measurable Y ∧
      P.map X = F ∧ P.map Y = G ∧ P[Y|MeasurableSpace.comap X inferInstance] =ᵐ[P] X := by
  obtain ⟨ν,hνF,hνG,ht⟩ := exists_coupling_law_continuous_tests false F G hF hG horder
  let P : Measure ((Fin d → ℝ) × (Fin d → ℝ)) := ν
  letI : IsProbabilityMeasure P := ν.property
  have hf : IdentDistrib Prod.fst id P F :=
    ⟨measurable_fst.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hνF⟩
  have hg : IdentDistrib Prod.snd id P G :=
    ⟨measurable_snd.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hνG⟩
  have hiF : Integrable Prod.fst P := hf.integrable_iff.mpr (integrable_identity F hF)
  have hiG : Integrable Prod.snd P := hg.integrable_iff.mpr (integrable_identity G hG)
  have hb : ∀ k (s : Set (Fin d → ℝ)), MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 k ∂P) = ∫ z in Prod.fst ⁻¹' s, z.2 k ∂P := by
    intro k s hs
    have hwc : Continuous (fun z : (Fin d → ℝ) × (Fin d → ℝ) => z.2 k-z.1 k) := by fun_prop
    have hw := (hiG.eval k).sub (hiF.eval k)
    have hh := borel_eq_of_continuous_eq P (fun z => z.2 k-z.1 k) hwc hw
      (fun ψ => ht ψ k (by simp)) s hs
    rw [integral_sub (hiG.eval k).integrableOn (hiF.eval k).integrableOn] at hh
    linarith
  refine ⟨(Fin d → ℝ) × (Fin d → ℝ),inferInstance,P,inferInstance,Prod.fst,Prod.snd,
    measurable_fst,measurable_snd,hνF,hνG,?_⟩
  exact vector_condExp_eq_of_borel_tests P Prod.fst Prod.snd measurable_fst hiF hiG hb

lemma icx_implies_submartingale {d : ℕ}
    (F G : Measure (Fin d → ℝ)) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : IsIntegrableDist F) (hG : IsIntegrableDist G) (horder : IcxLe F G) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : Ω → Fin d → ℝ), Measurable X ∧ Measurable Y ∧
      P.map X = F ∧ P.map Y = G ∧
      ∀ᵐ ω ∂P, CoordLe (X ω) (P[Y|MeasurableSpace.comap X inferInstance] ω) := by
  obtain ⟨ν,hνF,hνG,ht⟩ := exists_coupling_law_continuous_tests true F G hF hG horder
  let P : Measure ((Fin d → ℝ) × (Fin d → ℝ)) := ν
  letI : IsProbabilityMeasure P := ν.property
  have hf : IdentDistrib Prod.fst id P F :=
    ⟨measurable_fst.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hνF⟩
  have hg : IdentDistrib Prod.snd id P G :=
    ⟨measurable_snd.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hνG⟩
  have hiF : Integrable Prod.fst P := hf.integrable_iff.mpr (integrable_identity F hF)
  have hiG : Integrable Prod.snd P := hg.integrable_iff.mpr (integrable_identity G hG)
  have hb : ∀ k (s : Set (Fin d → ℝ)), MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 k ∂P) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 k ∂P := by
    intro k s hs
    have hwc : Continuous (fun z : (Fin d → ℝ) × (Fin d → ℝ) => z.2 k-z.1 k) := by fun_prop
    have hw := (hiG.eval k).sub (hiF.eval k)
    have hh := borel_test_of_continuous_tests P (fun z => z.2 k-z.1 k) hwc hw
      (fun ψ hψ => ht ψ k (fun _ => hψ)) s hs
    rw [integral_sub (hiG.eval k).integrableOn (hiF.eval k).integrableOn] at hh
    linarith
  refine ⟨(Fin d → ℝ) × (Fin d → ℝ),inferInstance,P,inferInstance,Prod.fst,Prod.snd,
    measurable_fst,measurable_snd,hνF,hνG,?_⟩
  exact vector_condExp_le_of_borel_tests P Prod.fst Prod.snd measurable_fst hiF hiG hb
end MultivariateStrassenForward
#print axioms MultivariateStrassenForward.cx_implies_martingale
#print axioms MultivariateStrassenForward.icx_implies_submartingale

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open PalmQueueing.Ordering MultivariateStrassenApproximation
namespace MultivariateStrassenReverse
lemma martingale_implies_cx {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (F G : Measure (Fin d → ℝ)) (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → Fin d → ℝ)
    (hmX : Measurable X) (hmY : Measurable Y) (hmapX : P.map X = F) (hmapY : P.map Y = G)
    (hCE : P[Y|MeasurableSpace.comap X inferInstance] =ᵐ[P] X) : CxLe F G := by
  have hdX : IdentDistrib X id P F :=
    ⟨hmX.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hmapX⟩
  have hdY : IdentDistrib Y id P G :=
    ⟨hmY.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hmapY⟩
  have hiY : Integrable Y P := hdY.integrable_iff.mpr (integrable_identity G hG)
  intro f hfc hiF hiG
  have hcv : ConvexOn ℝ univ f := hfc
  have hcont : Continuous f := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hcv)
  have hdFX := hdX.comp hcont.measurable
  have hdFY := hdY.comp hcont.measurable
  have hifX : Integrable (f ∘ X) P := hdFX.integrable_iff.mpr hiF
  have hifY : Integrable (f ∘ Y) P := hdFY.integrable_iff.mpr hiG
  let m := MeasurableSpace.comap X inferInstance
  have hm : m ≤ mΩ := hmX.comap_le
  letI : MeasurableSpace Ω := mΩ
  have hj := hcv.map_condExp_le_univ hm hcont.lowerSemicontinuous hiY hifY
  have hh : (f ∘ X) ≤ᵐ[P] P[f ∘ Y|m] := by
    filter_upwards [hj,hCE] with ω hω he
    change P[Y|m] ω = X ω at he
    change f (P[Y|m] ω) ≤ P[f ∘ Y|m] ω at hω
    rw [he] at hω
    exact hω
  have hineq := integral_mono_ae hifX integrable_condExp hh
  rw [integral_condExp hm] at hineq
  have hAf : (∫ ω, f (X ω) ∂P) = ∫ x, f x ∂F := hdFX.integral_eq
  have hBf : (∫ ω, f (Y ω) ∂P) = ∫ y, f y ∂G := hdFY.integral_eq
  change (∫ ω, f (X ω) ∂P) ≤ ∫ ω, f (Y ω) ∂P at hineq
  rw [hAf,hBf] at hineq
  exact hineq

lemma submartingale_implies_icx {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (F G : Measure (Fin d → ℝ)) (hF : IsIntegrableDist F) (hG : IsIntegrableDist G)
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → Fin d → ℝ)
    (hmX : Measurable X) (hmY : Measurable Y) (hmapX : P.map X = F) (hmapY : P.map Y = G)
    (hCE : ∀ᵐ ω ∂P, CoordLe (X ω) (P[Y|MeasurableSpace.comap X inferInstance] ω)) : IcxLe F G := by
  have hdX : IdentDistrib X id P F :=
    ⟨hmX.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hmapX⟩
  have hdY : IdentDistrib Y id P G :=
    ⟨hmY.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hmapY⟩
  have hiY : Integrable Y P := hdY.integrable_iff.mpr (integrable_identity G hG)
  intro f hfc hiF hiG
  have hcv : ConvexOn ℝ univ f := hfc.2
  have hmono : ∀ x y, CoordLe x y → f x ≤ f y := hfc.1
  have hcont : Continuous f := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hcv)
  have hdFX := hdX.comp hcont.measurable
  have hdFY := hdY.comp hcont.measurable
  have hifX : Integrable (f ∘ X) P := hdFX.integrable_iff.mpr hiF
  have hifY : Integrable (f ∘ Y) P := hdFY.integrable_iff.mpr hiG
  let m := MeasurableSpace.comap X inferInstance
  have hm : m ≤ mΩ := hmX.comap_le
  letI : MeasurableSpace Ω := mΩ
  have hj := hcv.map_condExp_le_univ hm hcont.lowerSemicontinuous hiY hifY
  have hh : (f ∘ X) ≤ᵐ[P] P[f ∘ Y|m] := by
    filter_upwards [hj,hCE] with ω hω he
    exact (hmono _ _ he).trans hω
  have hineq := integral_mono_ae hifX integrable_condExp hh
  rw [integral_condExp hm] at hineq
  have hAf : (∫ ω, f (X ω) ∂P) = ∫ x, f x ∂F := hdFX.integral_eq
  have hBf : (∫ ω, f (Y ω) ∂P) = ∫ y, f y ∂G := hdFY.integral_eq
  change (∫ ω, f (X ω) ∂P) ≤ ∫ ω, f (Y ω) ∂P at hineq
  rw [hAf,hBf] at hineq
  exact hineq
end MultivariateStrassenReverse
#print axioms MultivariateStrassenReverse.martingale_implies_cx
#print axioms MultivariateStrassenReverse.submartingale_implies_icx

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
open MultivariateStrassenForward MultivariateStrassenReverse

theorem solution {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G)
    (hFi : IsIntegrableDist F) (hGi : IsIntegrableDist G) :
    (CxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] X) ∧
    (IcxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω)
          (condExp (MeasurableSpace.comap X inferInstance) P Y ω)) := by
  letI : IsProbabilityMeasure F := hF
  letI : IsProbabilityMeasure G := hG
  constructor
  · constructor
    · exact cx_implies_martingale F G hFi hGi
    · rintro ⟨Ω,mΩ,P,hP,X,Y,hmX,hmY,hmapX,hmapY,hCE⟩
      letI : MeasurableSpace Ω := mΩ
      letI : IsProbabilityMeasure P := hP
      exact martingale_implies_cx F G hFi hGi P X Y hmX hmY hmapX hmapY hCE
  · constructor
    · exact icx_implies_submartingale F G hFi hGi
    · rintro ⟨Ω,mΩ,P,hP,X,Y,hmX,hmY,hmapX,hmapY,hCE⟩
      letI : MeasurableSpace Ω := mΩ
      letI : IsProbabilityMeasure P := hP
      exact submartingale_implies_icx F G hFi hGi P X Y hmX hmY hmapX hmapY hCE

#print axioms solution

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Theorem 4.2.2 (Strassen's `≤_cx` theorem)** (p.278). Let `F` and `G` be two integrable
distributions in `𝒟(ℝⁿ)`; `F ≤_cx G` (resp. `F ≤_icx G`) **if and only if** there exist two
`ℝⁿ`-valued random variables `X` and `Y` defined on the same probability space with distributions
`F` and `G` respectively, and such that `E[Y | X] = X` (resp. `E[Y | X] ≥ X`) a.s.

The convex order holds exactly when the larger distribution is a **martingale dilation** of the
smaller: `G` is obtained from `F` by spreading each point out without moving its conditional mean.
That is the classical Strassen representation, and it is what makes the convex order tractable —
comparison results for queues become induction arguments on a coupling, rather than analytic
manipulations of convolutions of c.d.f.'s.

Both clauses are in the statement, as the book states them together: the `≤_cx` case with
`E[Y | X] = X` and the `≤_icx` case with `E[Y | X] ≥ X`.

**Both directions are asserted.** The hard one is the construction of the coupling; a
one-directional statement would be the easy half, since Jensen's inequality gives `F ≤_cx G` from
any such pair immediately.

`E[Y | X]` is a **conditional expectation**, not an equality of expectations: the whole content is
that the identity holds pointwise a.s. given `X`.

**Integrability is a hypothesis here and not in Theorem 4.2.1.** The convex order needs first
moments; the stochastic order does not. The two theorems are not harmonised.

The book attributes both to Strassen and does not prove them: "The next two theorems on the
pathwise representation of stochastic orders are proved in Strassen (1965)." -/
example {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G)
    (hFi : IsIntegrableDist F) (hGi : IsIntegrableDist G) :
    (CxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] X) ∧
    (IcxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω)
          (condExp (MeasurableSpace.comap X inferInstance) P Y ω)) := by
  exact solution F G hF hG hFi hGi

end PalmQueueing.Ordering

#print axioms solution
