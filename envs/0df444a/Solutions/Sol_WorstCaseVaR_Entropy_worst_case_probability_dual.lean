-- Prove2me | solution 1 for WorstCaseVaR.Entropy.worst_case_probability_dual
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:05:42.064992+00:00
-- url     : https://prove2.me/submissions/c3cdd3a4-e57d-4ee9-beb5-42cf1659b5c5

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory InformationTheory

lemma aux_wcv_weak {α : Type*} [MeasurableSpace α] (P₀ P : Measure α) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P] {S : Set α} (hS : MeasurableSet S) {d : ℝ} (hd : 0 ≤ d)
    (hP : klDiv P P₀ ≤ ENNReal.ofReal d) (t : ℝ) :
    t * P.real S ≤ d + Real.log ((Real.exp t - 1) * P₀.real S + 1) := by
  have hne : klDiv P P₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hP
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
  have hKL : ∫ x, llr P P₀ x ∂P ≤ d := by
    have h1 := toReal_klDiv hac hint
    simp only [probReal_univ, add_sub_cancel_right] at h1
    rw [← h1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal hd] at this
  set f : α → ℝ := S.indicator (fun _ => t) with hf_def
  have hexp : (fun x => Real.exp (f x)) = fun x => S.indicator (fun _ => Real.exp t - 1) x + 1 := by
    funext x
    by_cases hx : x ∈ S <;> simp [f, hx]
  have hexp_int : Integrable (fun x => Real.exp (f x)) P₀ := by
    rw [hexp]
    exact ((integrable_const _).indicator hS).add (integrable_const _)
  have hexp_integral : ∫ x, Real.exp (f x) ∂P₀ = (Real.exp t - 1) * P₀.real S + 1 := by
    rw [hexp, integral_add ((integrable_const _).indicator hS) (integrable_const _),
      integral_indicator_const _ hS]
    simp [smul_eq_mul, mul_comm]
  have hf_int : Integrable f P := (integrable_const t).indicator hS
  have hf_integral : ∫ x, f x ∂P = t * P.real S := by
    rw [hf_def, integral_indicator_const _ hS, smul_eq_mul, mul_comm]
  have : IsProbabilityMeasure (P₀.tilted f) := isProbabilityMeasure_tilted hexp_int
  have hacQ : P ≪ P₀.tilted f := hac.trans (absolutelyContinuous_tilted hexp_int)
  have hintQ : Integrable (llr P (P₀.tilted f)) P :=
    integrable_llr_tilted_right hac hf_int hint hexp_int
  have hG := integral_llr_add_sub_measure_univ_nonneg hacQ hintQ
  rw [integral_llr_tilted_right hac hf_int hexp_int hint] at hG
  simp only [probReal_univ, add_sub_cancel_right] at hG
  rw [hf_integral, hexp_integral] at hG
  linarith

lemma aux_wcv_primal {α : Type*} [MeasurableSpace α] (P₀ : Measure α) [IsProbabilityMeasure P₀]
    {S : Set α} (hS : MeasurableSet S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * P₀.real S + b * (1 - P₀.real S) = 1) :
    ∃ P : Measure α, IsProbabilityMeasure P ∧
      klDiv P P₀ = ENNReal.ofReal (P₀.real S * klFun a + (1 - P₀.real S) * klFun b) ∧
      P.real S = a * P₀.real S := by
  classical
  set φ := P₀.real S with hφ
  have hφ0 : 0 ≤ φ := measureReal_nonneg
  have hφ1 : φ ≤ 1 := measureReal_le_one
  have hPS : P₀ S = ENNReal.ofReal φ := by rw [hφ, ofReal_measureReal]
  have hPSc : P₀ Sᶜ = ENNReal.ofReal (1 - φ) := by
    rw [← ofReal_measureReal, probReal_compl_eq_one_sub hS]
  let h : α → ENNReal := S.piecewise (fun _ => ENNReal.ofReal a) (fun _ => ENNReal.ofReal b)
  have hm : Measurable h := Measurable.piecewise hS measurable_const measurable_const
  have hlin : ∀ g : ENNReal → ENNReal,
      ∫⁻ x, g (h x) ∂P₀ = g (ENNReal.ofReal a) * ENNReal.ofReal φ
        + g (ENNReal.ofReal b) * ENNReal.ofReal (1 - φ) := by
    intro g
    rw [← lintegral_add_compl _ hS]
    have e1 : ∫⁻ x in S, g (h x) ∂P₀ = ∫⁻ x in S, g (ENNReal.ofReal a) ∂P₀ :=
      setLIntegral_congr_fun hS (fun x hx => by simp [h, hx])
    have e2 : ∫⁻ x in Sᶜ, g (h x) ∂P₀ = ∫⁻ x in Sᶜ, g (ENNReal.ofReal b) ∂P₀ :=
      setLIntegral_congr_fun hS.compl (fun x hx => by simp [h, Set.notMem_of_mem_compl hx])
    rw [e1, e2, setLIntegral_const, setLIntegral_const, hPS, hPSc]
  have huniv : P₀.withDensity h Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have := hlin id
    simp only [id] at this
    rw [this, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_add (mul_nonneg ha hφ0) (mul_nonneg hb (by linarith)), hab,
      ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure (P₀.withDensity h) := ⟨huniv⟩
  refine ⟨P₀.withDensity h, hprob, ?_, ?_⟩
  · rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous P₀ h)]
    have hae : (fun x => ENNReal.ofReal (klFun ((P₀.withDensity h).rnDeriv P₀ x).toReal))
        =ᵐ[P₀] fun x => ENNReal.ofReal (klFun (h x).toReal) := by
      filter_upwards [Measure.rnDeriv_withDensity P₀ hm] with x hx
      rw [hx]
    rw [lintegral_congr_ae hae, hlin (fun y => ENNReal.ofReal (klFun y.toReal))]
    simp only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
    rw [← ENNReal.ofReal_mul (klFun_nonneg ha), ← ENNReal.ofReal_mul (klFun_nonneg hb),
      ← ENNReal.ofReal_add (mul_nonneg (klFun_nonneg ha) hφ0)
        (mul_nonneg (klFun_nonneg hb) (by linarith))]
    congr 1
    ring
  · rw [measureReal_def, withDensity_apply _ hS]
    have e1 : ∫⁻ x in S, h x ∂P₀ = ∫⁻ x in S, ENNReal.ofReal a ∂P₀ :=
      setLIntegral_congr_fun hS (fun x hx => by simp [h, hx])
    rw [e1, setLIntegral_const, hPS, ← ENNReal.ofReal_mul ha, ENNReal.toReal_ofReal (mul_nonneg ha hφ0)]

lemma aux_wcv_sandwich (A B : Set ℝ)
    (hle : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (happrox : ∀ ε > 0, ∃ a ∈ A, ∃ b ∈ B, b < a + ε) :
    ∃ θ, IsLUB A θ ∧ IsGLB B θ := by
  obtain ⟨a0, ha0, b0, hb0, -⟩ := happrox 1 one_pos
  have hA : A.Nonempty := ⟨a0, ha0⟩
  have hbdd : BddAbove A := ⟨b0, fun a ha => hle a ha b0 hb0⟩
  refine ⟨sSup A, isLUB_csSup hA hbdd, ?_, ?_⟩
  · intro b hb
    exact csSup_le hA (fun a ha => hle a ha b hb)
  · intro c hc
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    obtain ⟨a, ha, b, hb, hlt⟩ := happrox ε hε
    have h1 : c ≤ b := hc hb
    have h2 : a ≤ sSup A := le_csSup hbdd ha
    linarith

lemma aux_wcv_scalar {φ d ε : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a * φ + b * (1 - φ) = 1 ∧
      φ * klFun a + (1 - φ) * klFun b ≤ d ∧
      ∃ lam : ℝ, 0 < lam ∧ dualValue d φ lam < a * φ + ε := by
  rcases eq_or_lt_of_le hφ0 with hφ | hφpos
  · -- φ = 0
    subst hφ
    refine ⟨1, 1, zero_le_one, zero_le_one, by ring, by simp [klFun_one]; exact hd, ε / (d + 1),
      by positivity, ?_⟩
    simp only [dualValue, mul_zero, zero_add, Real.log_one, add_zero]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  by_cases hB : -Real.log φ ≤ d
  · -- the conditional measure is feasible
    refine ⟨1 / φ, 0, by positivity, le_refl _, by field_simp; ring, ?_, ε / (d + 1),
      by positivity, ?_⟩
    · simp only [klFun_apply, Real.log_zero, mul_zero, zero_add, sub_zero, mul_one]
      rw [one_div, Real.log_inv]
      field_simp
      linarith
    · have hlam : 0 < ε / (d + 1) := by positivity
      set lam := ε / (d + 1) with hlam_def
      have he : 1 ≤ Real.exp (1 / lam) := Real.one_le_exp (by positivity)
      have hlog : Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ 1 / lam := by
        calc Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ Real.log (Real.exp (1 / lam)) := by
              apply Real.log_le_log (by nlinarith)
              nlinarith
          _ = 1 / lam := Real.log_exp _
      have h1 : lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ 1 := by
        calc lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ lam * (1 / lam) :=
              mul_le_mul_of_nonneg_left hlog hlam.le
          _ = 1 := by field_simp
      have h2 : lam * d < ε := by
        rw [hlam_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      have h3 : 1 / φ * φ = 1 := by field_simp
      simp only [dualValue]
      rw [h3]
      linarith
  push Not at hB
  have hφlt : φ < 1 := by
    have : Real.log φ < 0 := by linarith
    exact (Real.log_neg_iff hφpos).mp this
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- d = 0: the reference measure, λ → ∞
    subst hd0
    refine ⟨1, 1, zero_le_one, zero_le_one, by ring, by simp [klFun_one], ?_⟩
    have hL : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    set s := Real.log (1 + ε) / 2 with hs_def
    have hs : 0 < s := by positivity
    have hes : Real.exp s < 1 + ε := by
      calc Real.exp s < Real.exp (Real.log (1 + ε)) := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 + ε := Real.exp_log (by linarith)
    refine ⟨1 / s, by positivity, ?_⟩
    simp only [dualValue, mul_zero, zero_add, one_div_one_div, one_mul]
    have he1 : 1 ≤ Real.exp s := Real.one_le_exp hs.le
    have hpos : 0 < (Real.exp s - 1) * φ + 1 := by nlinarith
    have hl := Real.log_le_sub_one_of_pos hpos
    -- e^s - 1 ≤ s e^s
    have hkey : Real.exp s - 1 ≤ s * Real.exp s := by
      have := Real.add_one_le_exp (-s)
      have hmul : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos s]
    have h1 : 1 / s * Real.log ((Real.exp s - 1) * φ + 1) ≤ 1 / s * ((Real.exp s - 1) * φ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : 1 / s * ((Real.exp s - 1) * φ) ≤ Real.exp s * φ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs]
      nlinarith
    nlinarith
  · -- interior case: intermediate value theorem
    set F : ℝ → ℝ := fun p => p * Real.log p + (1 - p) * Real.log (1 - p)
      - p * Real.log φ - (1 - p) * Real.log (1 - φ) with hF
    have hFc : Continuous F := by
      have h1 : Continuous fun p : ℝ => p * Real.log p := Real.continuous_mul_log
      have h2 : Continuous fun p : ℝ => (1 - p) * Real.log (1 - p) :=
        Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
      exact ((h1.add h2).sub (continuous_id.mul continuous_const)).sub
        ((continuous_const.sub continuous_id).mul continuous_const)
    have hFφ : F φ = 0 := by simp only [hF]; ring
    have hF1 : F 1 = -Real.log φ := by simp [hF]
    have hmem : d ∈ Set.Icc (F φ) (F 1) := ⟨by rw [hFφ]; exact hd, by rw [hF1]; exact hB.le⟩
    obtain ⟨p, ⟨hpφ, hp1⟩, hFp⟩ := intermediate_value_Icc hφlt.le hFc.continuousOn hmem
    have hpφ' : φ < p := by
      rcases eq_or_lt_of_le hpφ with h | h
      · subst h; rw [hFφ] at hFp; linarith
      · exact h
    have hp1' : p < 1 := by
      rcases eq_or_lt_of_le hp1 with h | h
      · subst h; rw [hF1] at hFp; linarith
      · exact h
    have hp0 : 0 < p := by linarith
    have h1p : 0 < 1 - p := by linarith
    have h1φ : 0 < 1 - φ := by linarith
    refine ⟨p / φ, (1 - p) / (1 - φ), by positivity, by positivity, by field_simp; ring, ?_, ?_⟩
    · simp only [klFun_apply]
      rw [Real.log_div hp0.ne' hφpos.ne', Real.log_div h1p.ne' h1φ.ne']
      have : F p = d := hFp
      simp only [hF] at this
      field_simp
      linarith
    · set t := Real.log p + Real.log (1 - φ) - Real.log φ - Real.log (1 - p) with ht
      have htpos : 0 < t := by
        have := Real.log_lt_log hφpos hpφ'
        have := Real.log_lt_log h1p (show 1 - p < 1 - φ by linarith)
        linarith
      refine ⟨1 / t, by positivity, ?_⟩
      have het : Real.exp t = p * (1 - φ) / (φ * (1 - p)) := by
        rw [ht, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hp0, Real.exp_log h1φ,
          Real.exp_log hφpos, Real.exp_log h1p]
        field_simp
      have harg : (Real.exp t - 1) * φ + 1 = (1 - φ) / (1 - p) := by
        rw [het]
        field_simp
        ring
      simp only [dualValue, one_div_one_div]
      rw [harg, Real.log_div h1φ.ne' h1p.ne']
      have : F p = d := hFp
      simp only [hF] at this
      have hval : 1 / t * d + 1 / t * (Real.log (1 - φ) - Real.log (1 - p)) = p := by
        rw [← mul_add, ← this]
        field_simp
        rw [ht]
        ring
      rw [hval]
      have : p / φ * φ = p := by field_simp
      rw [this]
      linarith


lemma aux_wcv_main {α : Type*} [MeasurableSpace α] (P₀ : Measure α) [IsProbabilityMeasure P₀]
    {S : Set α} (hS : MeasurableSet S) {d : ℝ} (hd : 0 ≤ d) (ball : Set (Measure α))
    (hball : ∀ P, P ∈ ball ↔ (IsProbabilityMeasure P ∧ klDiv P P₀ ≤ ENNReal.ofReal d)) :
    ∃ θ : ℝ, IsLUB {p | ∃ P ∈ ball, P.real S = p} θ ∧
      IsGLB (dualValue d (P₀.real S) '' Set.Ioi 0) θ := by
  apply aux_wcv_sandwich
  · rintro a ⟨P, hPb, rfl⟩ b ⟨lam, hlam, rfl⟩
    obtain ⟨hPprob, hPkl⟩ := (hball P).mp hPb
    have hlam' : (0 : ℝ) < lam := hlam
    have h := aux_wcv_weak P₀ P hS hd hPkl (1 / lam)
    have h2 : lam * (1 / lam * P.real S) ≤ lam * (d + Real.log ((Real.exp (1 / lam) - 1) * P₀.real S + 1)) :=
      mul_le_mul_of_nonneg_left h hlam'.le
    have h3 : lam * (1 / lam * P.real S) = P.real S := by field_simp
    simp only [dualValue]
    linarith
  · intro ε hε
    have hφ0 : 0 ≤ P₀.real S := measureReal_nonneg
    have hφ1 : P₀.real S ≤ 1 := measureReal_le_one
    obtain ⟨a, b, ha, hb, hab, hkl, lam, hlam, hlt⟩ := aux_wcv_scalar hφ0 hφ1 hd hε
    obtain ⟨P, hPprob, hPkl, hPS⟩ := aux_wcv_primal P₀ hS ha hb hab
    refine ⟨a * P₀.real S, ⟨P, (hball P).mpr ⟨hPprob, ?_⟩, hPS⟩, dualValue d (P₀.real S) lam,
      ⟨lam, hlam, rfl⟩, hlt⟩
    rw [hPkl]
    exact ENNReal.ofReal_le_ofReal hkl

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem solution {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (d : ℝ) (hd : 0 ≤ d) (γ : ℝ) :
    ∃ θ : ℝ,
      IsLUB {p | ∃ P ∈ klBall xhat Γ d, P.real (lossSet w γ) = p} θ ∧
      IsGLB (dualValue d ((refGaussian xhat Γ).real (lossSet w γ)) '' Set.Ioi 0) θ := by
  have hprob : MeasureTheory.IsProbabilityMeasure (refGaussian xhat Γ) := by
    unfold refGaussian; infer_instance
  have hS : MeasurableSet (lossSet w γ) := by
    unfold lossSet
    exact measurableSet_le measurable_const (by fun_prop)
  exact aux_wcv_main (refGaussian xhat Γ) hS hd (klBall xhat Γ d) (fun P => Iff.rfl)
