-- Prove2me | solution 1 for ProbabilityTheory.integral_simplex_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:45:55.4345+00:00
-- url     : https://prove2.me/submissions/320a932d-a8f4-4ab4-b9f3-b18317fe75fd

-- Research directed by Alexander Richard Towell (queelius); formal proof by OpenAI Codex.
-- Eyal1990 supplied the entropy formulations and prior reduction strategy.
-- Mission background: Kris Johnson Ferreira, David Simchi-Levi and He Wang.
-- Lean and Mathlib supply the foundations. No novelty or independent human review claimed.
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
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
-- Adapted from Eyal1990 submission 262fb5e6-e541-4796-91c8-80c536056847; open child replaced by our completed proof.

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

lemma history_entropy
    {N K : ℕ}
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1) :
    0 ≤ finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
      finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a) := by
  classical
  have hhist : histSigma A D t ≤ histSigma A D (t + 1) := by
    unfold histSigma
    refine iSup_le fun s => iSup_le fun hs => ?_
    exact le_iSup_of_le s (le_iSup_of_le (Nat.lt_succ_of_lt hs) le_rfl)
  apply sub_nonneg.mpr
  exact EntropyCampaign.entropy_mono P
    (histSigma A D t) (histSigma A D (t + 1))
    hhist
    (fun ω a => oracleActionWeights xsel (θ ω) a)
    (by
      intro a
      cases a with
      | none =>
          change Measurable (fun ω => 1 - ∑ k : Fin K, xsel (θ ω) k)
          exact measurable_const.sub
            (Finset.measurable_sum Finset.univ fun k _ =>
              (measurable_pi_apply k).comp (hx.comp hθ))
      | some k =>
          exact (measurable_pi_apply k).comp (hx.comp hθ))
    (by
      intro ω a
      cases a with
      | none =>
          simp only [oracleActionWeights]
          exact sub_nonneg.mpr (hx1 (θ ω))
      | some k => exact hx0 (θ ω) k)
    (by
      intro ω
      simp only [Fintype.sum_option, oracleActionWeights]
      exact sub_add_cancel _ _)
-- Adapted from Eyal1990 submission 1ddcdfea-31d6-45e8-8bf1-7fbdc122c215; repaired the positive-factor cancellation for the pinned library API.

open MeasureTheory
open scoped BigOperators

private lemma simplex_entropy_bounds_aux
    {α : Type*} [Fintype α] [Nonempty α]
    (q : α → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a : α, q a = 1) :
    0 ≤ ∑ a : α, Real.negMulLog (q a) ∧
      (∑ a : α, Real.negMulLog (q a)) ≤ Real.log (Fintype.card α : ℝ) := by
  classical
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  constructor
  · apply Finset.sum_nonneg
    intro a _
    apply Real.negMulLog_nonneg (hq0 a)
    rw [← hq1]
    exact Finset.single_le_sum (fun b _ => hq0 b) (Finset.mem_univ a)
  · have hs : (∑ a : α, Real.negMulLog (n * q a)) ≤ 0 := by
      calc
        (∑ a : α, Real.negMulLog (n * q a)) ≤
            ∑ a : α, (1 - n * q a) := by
          apply Finset.sum_le_sum
          intro a _
          exact Real.negMulLog_le_one_sub_self (mul_nonneg hn.le (hq0 a))
        _ = 0 := by
          simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, n]
    have hsum : (∑ a : α, Real.negMulLog (n * q a)) =
        n * (∑ a : α, Real.negMulLog (q a)) + Real.negMulLog n := by
      simp_rw [Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq1]
      ring
    have hnlog : Real.negMulLog n = -n * Real.log n := rfl
    rw [hsum, hnlog] at hs
    change (∑ a : α, Real.negMulLog (q a)) ≤ Real.log n
    by_contra h
    have hp := mul_pos hn (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hs,hp]

lemma simplex_integral
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [Nonempty α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → α → ℝ)
    (hqMeas : ∀ a, Measurable (fun ω => q ω a))
    (hq0 : ∀ᵐ ω ∂P, ∀ a, 0 ≤ q ω a)
    (hq1 : ∀ᵐ ω ∂P, ∑ a : α, q ω a = 1) :
    0 ≤ MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ∧
      MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ≤
        Real.log (Fintype.card α : ℝ) := by
  classical
  let f : Ω → ℝ := fun ω => ∑ a : α, Real.negMulLog (q ω a)
  have hm : Measurable f := by
    exact Finset.measurable_sum Finset.univ (fun a _ =>
      Real.continuous_negMulLog.measurable.comp (hqMeas a))
  have hpoint : ∀ᵐ ω ∂P,
      0 ≤ f ω ∧ f ω ≤ Real.log (Fintype.card α : ℝ) := by
    filter_upwards [hq0, hq1] with ω hω0 hω1
    exact simplex_entropy_bounds_aux (q ω) hω0 hω1
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ f ω := hpoint.mono (fun _ h => h.1)
  have hupper : ∀ᵐ ω ∂P, f ω ≤ Real.log (Fintype.card α : ℝ) :=
    hpoint.mono (fun _ h => h.2)
  have hf : Integrable f P :=
    (integrable_const (Real.log (Fintype.card α : ℝ))).mono_nonneg
      hm.aestronglyMeasurable hnonneg hupper
  change 0 ≤ integral P f ∧ integral P f ≤ Real.log (Fintype.card α : ℝ)
  refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
  calc
    integral P f ≤ integral P (fun _ => Real.log (Fintype.card α : ℝ)) :=
      integral_mono_ae hf (integrable_const _) hupper
    _ = Real.log (Fintype.card α : ℝ) := by simp
theorem solution
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [Nonempty α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → α → ℝ)
    (hqMeas : ∀ a, Measurable (fun ω => q ω a))
    (hq0 : ∀ᵐ ω ∂P, ∀ a, 0 ≤ q ω a)
    (hq1 : ∀ᵐ ω ∂P, ∑ a : α, q ω a = 1) :
    0 ≤ MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ∧
      MeasureTheory.integral P (fun ω => ∑ a : α, Real.negMulLog (q ω a)) ≤
        Real.log (Fintype.card α : ℝ) := by
  exact simplex_integral P q hqMeas hq0 hq1
