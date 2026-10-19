-- Prove2me | solution 1 for OnlineNRM.TSFixed.finitePosteriorEntropy_scalar_mono
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:42:37.650406+00:00
-- url     : https://prove2.me/submissions/5584ff4c-1b2d-4ad2-b093-82d458bd2d56

-- Research directed by Alexander Richard Towell (queelius); formal proof by OpenAI Codex.
-- Eyal1990 supplied the entropy formulations and prior reduction strategy.
-- Mission background: Kris Johnson Ferreira, David Simchi-Levi and He Wang.
-- Lean and Mathlib supply the foundations. No novelty or independent human review claimed.
import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace EntropyCampaign
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

lemma int_bounded (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (h0 : ∀ᵐ ω ∂P, 0 ≤ f ω) (h1 : ∀ᵐ ω ∂P, f ω ≤ 1) : Integrable f P := by
  let : MeasurableSpace Ω := mΩ
  apply (integrable_const (1 : ℝ)).mono' hf
  filter_upwards [h0,h1] with ω h0 h1
  simpa [Real.norm_eq_abs,abs_of_nonneg h0] using h1

lemma cond_bounds (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ mΩ inferInstance f) (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    ∀ᵐ ω ∂P, (P[f | m]) ω ∈ Set.Icc (0:ℝ) 1 := by
  let : MeasurableSpace Ω := mΩ
  by_cases hm : m ≤ mΩ
  · have hi := int_bounded P f hf.aestronglyMeasurable (.of_forall h0) (.of_forall h1)
    have hu := condExp_mono (m := m) hi (integrable_const (1:ℝ)) (.of_forall h1)
    rw [condExp_const hm] at hu
    filter_upwards [condExp_nonneg (m := m) (.of_forall h0),hu] with ω h0 h1
    exact ⟨h0,h1⟩
  · rw [condExp_of_not_le hm]
    filter_upwards [] with ω
    simp

lemma entropy_int (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ mΩ inferInstance f) (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    Integrable (fun ω => Real.negMulLog ((P[f | m]) ω)) P := by
  let : MeasurableSpace Ω := mΩ
  have hb := cond_bounds P m f hf h0 h1
  apply int_bounded P _ (Real.continuous_negMulLog.comp_aestronglyMeasurable integrable_condExp.1)
  · filter_upwards [hb] with ω h
    exact Real.negMulLog_nonneg h.1 h.2
  · filter_upwards [hb] with ω h
    exact (Real.negMulLog_le_one_sub_self h.1).trans (by linarith [h.1])

lemma scalar_mono (m₁ m₂ : MeasurableSpace Ω) (hm : m₁ ≤ m₂)
    (f : Ω → ℝ) (hf : @Measurable Ω ℝ mΩ inferInstance f) (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    ∫ ω, Real.negMulLog ((P[f | m₂]) ω) ∂P ≤
      ∫ ω, Real.negMulLog ((P[f | m₁]) ω) ∂P := by
  let : MeasurableSpace Ω := mΩ
  by_cases hm₂ : m₂ ≤ mΩ
  · have hm₁ := hm.trans hm₂
    have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := P) (m := m₁)
      hm₁ Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
      ((cond_bounds P m₂ f hf h0 h1).mono fun ω h => h.1)
      isClosed_Ici integrable_condExp (entropy_int P m₂ f hf h0 h1)
    have hT := condExp_condExp_of_le (μ := P) (f := f) hm hm₂
    have hle : P[(fun ω => Real.negMulLog ((P[f | m₂]) ω)) | m₁] ≤ᵐ[P]
        (fun ω => Real.negMulLog ((P[f | m₁]) ω)) := by
      filter_upwards [hJ,hT] with ω hj ht
      simpa only [Function.comp_def,ht] using hj
    have h := integral_mono_ae integrable_condExp (entropy_int P m₁ f hf h0 h1) hle
    rwa [integral_condExp hm₁] at h
  · rw [condExp_of_not_le hm₂]
    simp only [Pi.zero_apply,Real.negMulLog_zero,integral_zero]
    apply integral_nonneg_of_ae
    filter_upwards [cond_bounds P m₁ f hf h0 h1] with ω h
    exact Real.negMulLog_nonneg h.1 h.2

lemma weight_le_one {α : Type*} [Fintype α] (w : Ω → α → ℝ)
    (h0 : ∀ ω a, 0 ≤ w ω a) (hs : ∀ ω, ∑ a, w ω a = 1) (ω : Ω) (a : α) : w ω a ≤ 1 := by
  let : MeasurableSpace Ω := mΩ
  rw [← hs ω]
  exact Finset.single_le_sum (fun a _ => h0 ω a) (Finset.mem_univ a)

lemma entropy_sum {α : Type*} [Fintype α] (m : MeasurableSpace Ω) (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a)) (h0 : ∀ ω a, 0 ≤ w ω a)
    (hs : ∀ ω, ∑ a, w ω a = 1) :
    @finitePosteriorEntropy Ω α mΩ inferInstance P m w = ∑ a, ∫ ω, Real.negMulLog ((P[fun ω' => w ω' a | m]) ω) ∂P := by
  let : MeasurableSpace Ω := mΩ
  unfold finitePosteriorEntropy
  exact integral_finsetSum _ (fun a _ => entropy_int P m _ (hw a) (fun ω => h0 ω a)
    (fun ω => weight_le_one w h0 hs ω a))

lemma entropy_mono {α : Type*} [Fintype α] (m₁ m₂ : MeasurableSpace Ω)
    (hm : m₁ ≤ m₂) (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a)) (h0 : ∀ ω a, 0 ≤ w ω a)
    (hs : ∀ ω, ∑ a, w ω a = 1) :
    @finitePosteriorEntropy Ω α mΩ inferInstance P m₂ w ≤ @finitePosteriorEntropy Ω α mΩ inferInstance P m₁ w := by
  let : MeasurableSpace Ω := mΩ
  rw [entropy_sum P m₁ w hw h0 hs,entropy_sum P m₂ w hw h0 hs]
  exact Finset.sum_le_sum fun a _ => scalar_mono P m₁ m₂ hm _ (hw a)
    (fun ω => h0 ω a) (fun ω => weight_le_one w h0 hs ω a)
end EntropyCampaign
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₁ m₂ : MeasurableSpace Ω) (hm : m₁ ≤ m₂)
    (f : Ω → ℝ)
    (hfmeas : @Measurable Ω ℝ mΩ inferInstance f)
    (hf0 : ∀ ω, 0 ≤ f ω)
    (hf1 : ∀ ω, f ω ≤ 1) :
    ∫ ω, Real.negMulLog ((P[fun ω' => f ω' | m₂]) ω) ∂P ≤
      ∫ ω, Real.negMulLog ((P[fun ω' => f ω' | m₁]) ω) ∂P := by
  let : MeasurableSpace Ω := mΩ
  exact EntropyCampaign.scalar_mono P m₁ m₂ hm f hfmeas hf0 hf1
