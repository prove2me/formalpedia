-- Prove2me | solution 1 for StabGen.Entropy.pinsker_L1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:58:14.895548+00:00
-- url     : https://prove2.me/submissions/fbfc7437-72d0-4fd6-8fa2-b088d96258c5

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting
import Definitions.Def_StabGen_Entropy_Model

open MeasureTheory InformationTheory ExploreFirst.FundIneq
open scoped ENNReal

lemma ber_prob' (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsProbabilityMeasure (bernoulliLaw a) := by
  constructor
  simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

/-- the KL divergence between two Bernoulli laws with `q ∈ (0,1)`, `p ∈ (0,1)` -/
lemma klBer_eq (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBer p q = ENNReal.ofReal (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  classical
  haveI := ber_prob' p hp0 hp1
  haveI := ber_prob' q hq0.le hq1.le
  set f : ℝ → ℝ≥0∞ := fun x => if x = 1 then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))
    with hf
  have hfm : Measurable f := Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have hwd : (bernoulliLaw q).withDensity f = bernoulliLaw p := by
    ext s hs
    rw [withDensity_apply _ hs, bernoulliLaw, Measure.restrict_add, lintegral_add_measure,
      Measure.restrict_smul, Measure.restrict_smul, lintegral_smul_measure, lintegral_smul_measure]
    simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [restrict_dirac' hs, restrict_dirac' hs]
    have hf1 : f 1 = ENNReal.ofReal (p / q) := by simp [hf]
    have hf0 : f 0 = ENNReal.ofReal ((1 - p) / (1 - q)) := by simp [hf]
    have e1 : ENNReal.ofReal q * ENNReal.ofReal (p / q) = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_mul hq0.le]; congr 1; field_simp
    have e0 : ENNReal.ofReal (1 - q) * ENNReal.ofReal ((1 - p) / (1 - q)) = ENNReal.ofReal (1 - p) := by
      rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (by linarith : (1:ℝ) - q ≠ 0), mul_one]
    by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s <;>
      simp [h1, h0, Measure.dirac_apply' _ hs, lintegral_dirac, hf1, hf0, e1, e0]
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [← hwd]; exact withDensity_absolutelyContinuous _ _
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] f := by
    rw [← hwd]; exact Measure.rnDeriv_withDensity _ hfm
  have hrnp : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw p] f := hac.ae_le hrn
  have hllr : llr (bernoulliLaw p) (bernoulliLaw q) =ᵐ[bernoulliLaw p] fun x => Real.log (f x).toReal := by
    filter_upwards [hrnp] with x hx; simp [llr, hx]
  have hint : Integrable (fun x => Real.log (f x).toReal) (bernoulliLaw p) := by
    rw [bernoulliLaw]
    exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  rw [klBer, klDiv_of_ac_of_integrable hac (hint.congr hllr.symm), integral_congr_ae hllr,
    probReal_univ, probReal_univ, add_sub_cancel_right]
  congr 1
  rw [bernoulliLaw, integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [hf, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - p),
    ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith : (0:ℝ) ≤ 1 - q))]


open Real Set

/-- the binary divergence as a function of the second argument -/
noncomputable def binKL (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

lemma binKL_deriv (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt (fun x => binKL a x - 2 * (a - x) ^ 2)
      ((b - a) * (1 / (b * (1 - b)) - 4)) b := by
  set g : ℝ → ℝ := fun x => a * Real.log a - a * Real.log x + (1 - a) * Real.log (1 - a)
    - (1 - a) * Real.log (1 - x) - 2 * (a - x) ^ 2 with hg
  have hlog1 : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - b)) b := by
    have hd : HasDerivAt (fun x => 1 - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub 1
    have := hd.log (by linarith)
    simpa using this
  have hsq : HasDerivAt (fun x => 2 * (a - x) ^ 2) (2 * (2 * (a - b) * (-1))) b := by
    have hd : HasDerivAt (fun x => a - x) (-1) b := by simpa using (hasDerivAt_id b).const_sub a
    have := (hd.pow 2).const_mul 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hgd : HasDerivAt g (-(a * b⁻¹) - (1 - a) * (-1 / (1 - b)) - 2 * (2 * (a - b) * (-1))) b := by
    have := ((((hasDerivAt_const b (a * Real.log a)).sub ((Real.hasDerivAt_log hb0.ne').const_mul a)).add
      (hasDerivAt_const b ((1 - a) * Real.log (1 - a)))).sub (hlog1.const_mul (1 - a))).sub hsq
    refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv (by ring)
    simp [hg]
  have hev : (fun x => binKL a x - 2 * (a - x) ^ 2) =ᶠ[nhds b] g := by
    filter_upwards [Ioo_mem_nhds hb0 hb1] with x hx
    simp only [binKL, hg]
    rw [Real.log_div ha0.ne' hx.1.ne', Real.log_div (by linarith) (by linarith [hx.2])]; ring
  refine (hgd.congr_of_eventuallyEq hev).congr_deriv ?_
  have : (1 - b) ≠ 0 := by linarith
  have : b ≠ 0 := hb0.ne'
  field_simp; ring

/-- binary Pinsker: `kl(a,b) ≥ 2 (a-b)²` on the open square -/
theorem binary_pinsker (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  set f := fun x => binKL a x - 2 * (a - x) ^ 2 with hf
  have hfa : f a = 0 := by simp [hf, binKL, div_self ha0.ne', div_self (by linarith : (1:ℝ) - a ≠ 0)]
  have hfac : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ 1 / (x * (1 - x)) - 4 := by
    intro x hx
    have hp : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    rw [sub_nonneg, le_div_iff₀ hp]; nlinarith [sq_nonneg (x - 1 / 2)]
  have hcont : ∀ c d, 0 < c → d < 1 → ContinuousOn f (Icc c d) := by
    intro c d hc hd x hx
    exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  rcases le_total a b with hab | hba
  · -- f increases on [a, b]
    have hmono : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcont a b ha0 hb1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonneg (by linarith [hx.1]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hf] at this hfa; linarith
  · -- f decreases on [b, a]
    have hanti : AntitoneOn f (Icc b a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc b a) (hcont b a hb0 ha1)
      · intro x hx; rw [interior_Icc] at hx
        exact (binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx; rw [interior_Icc] at hx
        rw [(binKL_deriv a x ha0 ha1 (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (hfac x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have := hanti ⟨le_rfl, hba⟩ ⟨hba, le_rfl⟩ hba
    simp only [hf] at this hfa; linarith

/-- binary Pinsker on the closed range of the first argument -/
theorem binary_pinsker' (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  -- `a ↦ binKL a b - 2 (a - b)^2` is continuous on ℝ
  have hc : Continuous (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2) := by
    have e : (fun x : ℝ => binKL x b) = fun x => (x * Real.log x - x * Real.log b)
        + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b)) := by
      funext x
      simp only [binKL]
      rcases eq_or_ne x 0 with h0 | h0
      · subst h0; simp
      rcases eq_or_ne (1 - x) 0 with h1 | h1
      · rw [h1]; simp [Real.log_div h0 hb0.ne']; ring
      rw [Real.log_div h0 hb0.ne', Real.log_div h1 (by linarith)]; ring
    rw [show (fun x : ℝ => binKL x b - 2 * (x - b) ^ 2)
        = fun x => ((x * Real.log x - x * Real.log b)
          + ((1 - x) * Real.log (1 - x) - (1 - x) * Real.log (1 - b))) - 2 * (x - b) ^ 2 from by
        funext x; rw [show binKL x b = _ from congrFun e x]]
    have h1 := Real.continuous_mul_log
    have h2 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
      h1.comp (continuous_const.sub continuous_id)
    fun_prop
  -- the interior points are dense near the endpoints
  have hclosed : IsClosed {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} :=
    isClosed_le continuous_const hc
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {x : ℝ | 0 ≤ binKL x b - 2 * (x - b) ^ 2} := by
    intro x hx
    have := binary_pinsker x b hx.1 hx.2 hb0 hb1
    simp only [Set.mem_setOf_eq]; nlinarith [sq_nonneg (x - b), sq_nonneg (b - x)]
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  have := hcl ⟨ha0, ha1⟩
  simp only [Set.mem_setOf_eq] at this
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - a)]


open MeasureTheory InformationTheory

theorem solution {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SigmaFinite ν]
    (g g' : Θ → ℝ) (hg : StabGen.Entropy.IsDensity ν g) (hg' : StabGen.Entropy.IsDensity ν g') :
    ENNReal.ofReal ((1 / 2) * (∫ θ, |g θ - g' θ| ∂ν) ^ 2) ≤ StabGen.Entropy.relEntropy ν g g' := by
  classical
  obtain ⟨gm, gnn, gint, g1⟩ := hg
  obtain ⟨gm', gnn', gint', g1'⟩ := hg'
  set μ := ν.withDensity (fun θ => ENNReal.ofReal (g θ)) with hμ
  set μ' := ν.withDensity (fun θ => ENNReal.ofReal (g' θ)) with hμ'
  set A := {θ | g' θ < g θ} with hA
  have hAm : MeasurableSet A := measurableSet_lt gm' gm
  set a := ∫ θ in A, g θ ∂ν with ha
  set b := ∫ θ in A, g' θ ∂ν with hb
  -- masses of A and its complement
  have hmass : ∀ (f : Θ → ℝ), Measurable f → (∀ θ, 0 ≤ f θ) → Integrable f ν → ∫ θ, f θ ∂ν = 1 →
      ν.withDensity (fun θ => ENNReal.ofReal (f θ)) A = ENNReal.ofReal (∫ θ in A, f θ ∂ν) ∧
      ν.withDensity (fun θ => ENNReal.ofReal (f θ)) Aᶜ = ENNReal.ofReal (1 - ∫ θ in A, f θ ∂ν) := by
    intro f fm fnn fint f1
    have hA' : ν.withDensity (fun θ => ENNReal.ofReal (f θ)) A = ENNReal.ofReal (∫ θ in A, f θ ∂ν) := by
      rw [withDensity_apply _ hAm, ofReal_integral_eq_lintegral_ofReal fint.integrableOn
        (Filter.Eventually.of_forall fnn)]
    refine ⟨hA', ?_⟩
    rw [withDensity_apply _ hAm.compl, ← ofReal_integral_eq_lintegral_ofReal fint.integrableOn
        (Filter.Eventually.of_forall fnn)]
    congr 1
    have := integral_add_compl hAm fint
    linarith
  obtain ⟨hμA, hμAc⟩ := hmass g gm gnn gint g1
  obtain ⟨hμ'A, hμ'Ac⟩ := hmass g' gm' gnn' gint' g1'
  have ha0 : 0 ≤ a := setIntegral_nonneg hAm (fun θ _ => gnn θ)
  have hb0 : 0 ≤ b := setIntegral_nonneg hAm (fun θ _ => gnn' θ)
  have hint_c : ∀ f : Θ → ℝ, (∀ θ, 0 ≤ f θ) → Integrable f ν → ∫ θ, f θ ∂ν = 1 → ∫ θ in A, f θ ∂ν ≤ 1 := by
    intro f fnn fint f1
    have := integral_add_compl hAm fint
    have : 0 ≤ ∫ θ in Aᶜ, f θ ∂ν := setIntegral_nonneg hAm.compl (fun θ _ => fnn θ)
    linarith
  have ha1 : a ≤ 1 := hint_c g gnn gint g1
  have hb1 : b ≤ 1 := hint_c g' gnn' gint' g1'
  have hab : b ≤ a := by
    rw [ha, hb, ← sub_nonneg, ← integral_sub gint.integrableOn gint'.integrableOn]
    exact setIntegral_nonneg hAm (fun θ hθ => by have : g' θ < g θ := hθ; linarith)
  -- the L1 distance
  have hL1 : ∫ θ, |g θ - g' θ| ∂ν = 2 * (a - b) := by
    have hd : Integrable (fun θ => g θ - g' θ) ν := gint.sub gint'
    have e1 := integral_add_compl hAm hd.abs
    have e2 := integral_add_compl hAm hd
    have hA1 : ∫ θ in A, |g θ - g' θ| ∂ν = ∫ θ in A, (g θ - g' θ) ∂ν :=
      setIntegral_congr_fun hAm (fun θ hθ => abs_of_pos (by have : g' θ < g θ := hθ; linarith))
    have hA2 : ∫ θ in Aᶜ, |g θ - g' θ| ∂ν = -∫ θ in Aᶜ, (g θ - g' θ) ∂ν := by
      rw [← integral_neg]
      exact setIntegral_congr_fun hAm.compl (fun θ hθ => by
        have : ¬ (g' θ < g θ) := hθ
        rw [abs_of_nonpos (by linarith)])
    have htot : ∫ θ, (g θ - g' θ) ∂ν = 0 := by rw [integral_sub gint gint', g1, g1', sub_self]
    have hAd : ∫ θ in A, (g θ - g' θ) ∂ν = a - b := integral_sub gint.integrableOn gint'.integrableOn
    linarith
  rw [hL1, show (1 / 2 : ℝ) * (2 * (a - b)) ^ 2 = 2 * (a - b) ^ 2 by ring]
  -- push forward by the indicator of A
  set φ : Θ → ℝ := A.indicator (fun _ => (1 : ℝ)) with hφ
  have hφm : Measurable φ := measurable_const.indicator hAm
  have hpush : ∀ (m : Measure Θ) (c : ℝ), m A = ENNReal.ofReal c → m Aᶜ = ENNReal.ofReal (1 - c) →
      m.map φ = ExploreFirst.FundIneq.bernoulliLaw c := by
    intro m c h1 h0
    ext s hs
    rw [Measure.map_apply hφm hs]
    simp only [ExploreFirst.FundIneq.bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases h1s : (1 : ℝ) ∈ s <;> by_cases h0s : (0 : ℝ) ∈ s
    · have : φ ⁻¹' s = Set.univ := by
        ext θ; simp only [Set.mem_preimage, Set.mem_univ, iff_true, hφ]
        by_cases hθ : θ ∈ A <;> simp [hθ, h1s, h0s]
      rw [this, ← Set.union_compl_self A, measure_union disjoint_compl_right hAm.compl, h1, h0]
      simp [h1s, h0s]
    · have : φ ⁻¹' s = A := by
        ext θ; simp only [Set.mem_preimage, hφ]
        by_cases hθ : θ ∈ A <;> simp [hθ, h1s, h0s]
      rw [this, h1]; simp [h1s, h0s]
    · have : φ ⁻¹' s = Aᶜ := by
        ext θ; simp only [Set.mem_preimage, hφ, Set.mem_compl_iff]
        by_cases hθ : θ ∈ A <;> simp [hθ, h1s, h0s]
      rw [this, h0]; simp [h1s, h0s]
    · have : φ ⁻¹' s = ∅ := by
        ext θ; simp only [Set.mem_preimage, hφ, Set.mem_empty_iff_false, iff_false]
        by_cases hθ : θ ∈ A <;> simp [hθ, h1s, h0s]
      rw [this]; simp [h1s, h0s]
  haveI : IsFiniteMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal gint (Filter.Eventually.of_forall gnn), g1]; simp⟩
  haveI : IsFiniteMeasure μ' := ⟨by
    rw [hμ', withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal gint' (Filter.Eventually.of_forall gnn'), g1']; simp⟩
  have hdpi := klDiv_map_le μ μ' hφm
  rw [hpush μ a hμA hμAc, hpush μ' b hμ'A hμ'Ac] at hdpi
  refine le_trans ?_ hdpi
  -- binary Pinsker on Bernoulli laws
  rcases eq_or_lt_of_le hab with hba | hba
  · rw [hba, sub_self]; simp
  rcases eq_or_lt_of_le hb0 with hb00 | hbpos
  · -- b = 0 < a: not absolutely continuous
    rw [← hb00]
    have hnac : ¬ ExploreFirst.FundIneq.bernoulliLaw a ≪ ExploreFirst.FundIneq.bernoulliLaw 0 := by
      intro hac
      have h0 : ExploreFirst.FundIneq.bernoulliLaw 0 {1} = 0 := by
        simp [ExploreFirst.FundIneq.bernoulliLaw]
      have := hac h0
      simp [ExploreFirst.FundIneq.bernoulliLaw] at this
      linarith [hb00 ▸ hba]
    show _ ≤ klDiv _ _
    rw [klDiv_of_not_ac hnac]; exact le_top
  have hb1' : b < 1 := lt_of_lt_of_le hba ha1
  show _ ≤ ExploreFirst.FundIneq.klBer a b
  rw [klBer_eq a b ha0 ha1 hbpos hb1']
  exact ENNReal.ofReal_le_ofReal (binary_pinsker' a b ha0 ha1 hbpos hb1')
