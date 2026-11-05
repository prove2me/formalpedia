-- Prove2me | solution 1 for WassFSG.Grad.corollary_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:18:10.415203+00:00
-- url     : https://prove2.me/submissions/fc5724b6-5247-496e-8c73-57b39c383cd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Grad_Rademacher
import Theorems.Thm_WassFSG_Grad_theorem_3
import Theorems.Thm_WassFSG_Grad_lemma_2
import Theorems.Thm_WassFSG_Grad_lemma_7
import Theorems.Thm_RadGauss_RiskBound_mcdiarmid_inequality

open MeasureTheory

namespace WassFSGCor6Aux

open WassFSG.Grad

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z]

/-- Under Assumption 2 the gradient map is Lipschitz, hence continuous. -/
lemma continuous_fderiv_of_gradLip {ħ : ℝ} {F : Set (Z → ℝ)} (hF : GradLipBound ħ F)
    {f : Z → ℝ} (hf : f ∈ F) : Continuous (fderiv ℝ f) := by
  have hL : LipschitzWith (Real.toNNReal ħ) (fderiv ℝ f) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hF.1.le]
    exact (hF.2 f hf).2 y x
  exact hL.continuous

/-- Integral against the empirical measure is the sample average. -/
lemma integral_empMeasure {n : ℕ} (hn : 0 < n) (z : Fin n → Z) (φ : Z → ℝ) :
    ∫ x, φ x ∂(WassFSG.Lip.empMeasure z) = (1 / (n : ℝ)) * ∑ i, φ (z i) := by
  unfold WassFSG.Lip.empMeasure
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul]
  · intro i _
    exact integrable_dirac enorm_lt_top

/-- The empirical measure is in `P₂(Z)`. -/
lemma isP2_empMeasure {n : ℕ} (hn : 0 < n) (z : Fin n → Z) :
    IsP2 (WassFSG.Lip.empMeasure z) := by
  have hn' : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨?_⟩, ?_⟩
  · unfold WassFSG.Lip.empMeasure
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top n)
  · unfold WassFSG.Lip.empMeasure
    rw [lintegral_smul_measure, lintegral_finsetSum_measure]
    simp only [lintegral_dirac]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact ENNReal.inv_lt_top.mpr (by exact_mod_cast hn)
    · exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.pow_lt_top enorm_lt_top

lemma gradNorm_empMeasure {n : ℕ} (hn : 0 < n) (z : Fin n → Z) (f : Z → ℝ) :
    gradNorm (WassFSG.Lip.empMeasure z) f = empGradNorm z f := by
  unfold gradNorm empGradNorm
  rw [integral_empMeasure hn z (fun x => ‖fderiv ℝ f x‖ ^ 2)]

/-- Replacing one sample point changes a sample average of a `[0, M]`-valued function by at
most `M / n`. -/
lemma empMean_update_le {n : ℕ} (hn : 0 < n) (h : Z → ℝ) (M : ℝ)
    (hh : ∀ z, 0 ≤ h z ∧ h z ≤ M) (x : Fin n → Z) (i : Fin n) (a : Z) :
    |WassFSG.Lip.empMean x h - WassFSG.Lip.empMean (Function.update x i a) h| ≤ M / n := by
  classical
  unfold WassFSG.Lip.empMean
  have hsum : ∑ j, h (Function.update x i a j) = ∑ j, h (x j) - h (x i) + h a := by
    have e1 : (fun j => h (Function.update x i a j)) =
        Function.update (fun j => h (x j)) i (h a) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [e1, Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => h (x j))]
    ring
  rw [hsum]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have e2 : 1 / (n : ℝ) * ∑ j, h (x j) - 1 / (n : ℝ) * (∑ j, h (x j) - h (x i) + h a)
      = (h (x i) - h a) / n := by
    field_simp; ring
  rw [e2, abs_div, abs_of_pos hnr]
  apply div_le_div_of_nonneg_right _ hnr.le
  rw [abs_le]
  constructor <;> linarith [hh (x i), hh a]

/-- Extended integral of a bounded measurable real function is its Bochner integral. -/
lemma extIntegral_coe {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ)
    (hφ : Integrable φ ν) :
    ModelRiskOT.Duality.extIntegral ν (fun x => (φ x : EReal)) = ((∫ x, φ x ∂ν : ℝ) : EReal) := by
  unfold ModelRiskOT.Duality.extIntegral
  have h1 : ∀ x, (-(φ x : EReal)) = ((-φ x : ℝ) : EReal) := fun x => (EReal.coe_neg _).symm
  simp only [h1, EReal.real_coe_toENNReal]
  have hA := hφ.lintegral_lt_top
  have hB := hφ.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at hB
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ,
    ← EReal.coe_ennreal_toReal hA.ne, ← EReal.coe_ennreal_toReal hB.ne]
  exact (EReal.coe_sub _ _).symm

/-- If `1 - e²/g² < δ` with `0 ≤ δ < 1/2`, then `g ≤ e (1 + δ)`. -/
lemma le_mul_one_add_of_dev (gn e δ : ℝ) (hgn : 0 < gn) (he : 0 ≤ e) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 / 2) (hdev : 1 - e ^ 2 / gn ^ 2 < δ) : gn ≤ e * (1 + δ) := by
  have hq : 0 < gn ^ 2 := by positivity
  have hgn2 : gn ^ 2 * (1 - δ) ≤ e ^ 2 := by
    have : 1 - δ < e ^ 2 / gn ^ 2 := by linarith
    rw [lt_div_iff₀ hq] at this
    linarith
  have hq0 : 0 ≤ 1 - δ - δ ^ 2 := by nlinarith
  have hpoly : 1 ≤ (1 - δ) * (1 + δ) ^ 2 := by nlinarith [mul_nonneg hδ0 hq0]
  have h1 : gn ^ 2 ≤ gn ^ 2 * ((1 - δ) * (1 + δ) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hpoly (sq_nonneg gn)
    linarith
  have h2 : gn ^ 2 * ((1 - δ) * (1 + δ) ^ 2) ≤ e ^ 2 * (1 + δ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hgn2 (sq_nonneg (1 + δ))
    linarith
  have hsq : gn ^ 2 ≤ (e * (1 + δ)) ^ 2 := by rw [mul_pow]; linarith
  exact (pow_le_pow_iff_left₀ hgn.le (mul_nonneg he (by linarith)) two_ne_zero).mp hsq

end WassFSGCor6Aux

open WassFSG.Grad

theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : IsT2 τ Ptrue)
    (F : Set (Z → ℝ)) (ħ : ℝ) (hF : GradLipBound ħ F)
    (hpos : ∀ f ∈ F, 0 < gradNorm Ptrue f)
    (γ₂ : ℝ) (hγ₂ : 0 < γ₂) (hbound : ∀ f ∈ F, gradNorm Ptrue f ≤ γ₂)
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (h5 : SubRootLocalComplexity Ptrue n F ψ)
    (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar) (t : ℝ) (ht : 0 < t)
    (RG : ℝ) (hRG : WassFSG.Lip.expectedRad Ptrue n (gradClass Ptrue F) = (RG : EReal))
    (κg : ℝ) (hκg : 0 < κg)
    (hκ : ∀ f ∈ F, ∀ z : Z, ‖fderiv ℝ f z‖ / gradNorm Ptrue f ≤ κg)
    (hsmall : 2 * RG + κg ^ 2 * Real.sqrt (t / (2 * n)) < 1 / 2) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ ((∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
              + rhoTilde ħ τ t RG rstar κg n * empGradNorm z f
              + 4 * rstar + 2 * epsN ħ τ t RG n) ∧
            (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤ (WassFSG.Lip.empMean z f : EReal)
              + regularizer (WassFSG.Lip.empMeasure z) (rhoTilde ħ τ t RG rstar κg n) f
              + ((4 * rstar + 2 * epsN ħ τ t RG n
                  + ħ * rhoTilde ħ τ t RG rstar κg n ^ 2 : ℝ) : EReal)))}
      ≤ ENNReal.ofReal (((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) + 1) * Real.exp (-t)) := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | ⟨f0, hf0⟩
  · subst hFe
    simp
  set μn := Measure.pi fun _ : Fin n => Ptrue with hμn
  set G := gradClass Ptrue F with hGdef
  set M : ℝ := κg ^ 2 with hMdef
  set s : ℝ := κg ^ 2 * Real.sqrt (t / (2 * n)) with hsdef
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hMpos : 0 < M := by positivity
  -- the normalized gradient functions
  set g : (Z → ℝ) → Z → ℝ := fun f z => ‖fderiv ℝ f z‖ ^ 2 / gradNorm Ptrue f ^ 2 with hgdef
  have hgG : ∀ f ∈ F, g f ∈ G := fun f hf => ⟨f, hf, rfl⟩
  have hGg : ∀ h ∈ G, ∃ f ∈ F, h = g f := fun h hh => hh
  have hg_bd : ∀ f ∈ F, ∀ z, 0 ≤ g f z ∧ g f z ≤ M := by
    intro f hf z
    refine ⟨by positivity, ?_⟩
    have h1 : 0 ≤ ‖fderiv ℝ f z‖ / gradNorm Ptrue f := div_nonneg (norm_nonneg _) (hpos f hf).le
    have h2 := pow_le_pow_left₀ h1 (hκ f hf z) 2
    simp only [hgdef]
    rw [← div_pow]
    exact h2
  have hg_cont : ∀ f ∈ F, Continuous (g f) := by
    intro f hf
    exact ((continuous_norm.comp
      (WassFSGCor6Aux.continuous_fderiv_of_gradLip hF hf)).pow 2).div_const _
  have hg_int : ∀ f ∈ F, Integrable (g f) Ptrue := by
    intro f hf
    refine Integrable.of_bound (hg_cont f hf).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_bd f hf z).1]
    exact (hg_bd f hf z).2
  have hg_one : ∀ f ∈ F, ∫ z, g f z ∂Ptrue = 1 := by
    intro f hf
    have hp := hpos f hf
    unfold gradNorm at hp
    have hI : 0 < ∫ z, ‖fderiv ℝ f z‖ ^ 2 ∂Ptrue := Real.sqrt_pos.mp hp
    simp only [hgdef]
    rw [integral_div]
    unfold gradNorm
    rw [Real.sq_sqrt hI.le]
    exact div_self hI.ne'
  have hG_bd : ∀ h ∈ G, ∀ z, 0 ≤ h z ∧ h z ≤ M := by
    intro h hh z
    obtain ⟨f, hf, rfl⟩ := hGg h hh
    exact hg_bd f hf z
  have hG_one : ∀ h ∈ G, ∫ z, h z ∂Ptrue = 1 := by
    intro h hh
    obtain ⟨f, hf, rfl⟩ := hGg h hh
    exact hg_one f hf
  have hG_cont : ∀ h ∈ G, Continuous h := by
    intro h hh
    obtain ⟨f, hf, rfl⟩ := hGg h hh
    exact hg_cont f hf
  have hG_int : ∀ h ∈ G, Integrable h Ptrue := by
    intro h hh
    obtain ⟨f, hf, rfl⟩ := hGg h hh
    exact hg_int f hf
  have hempMean_nonneg : ∀ h ∈ G, ∀ z : Fin n → Z, 0 ≤ WassFSG.Lip.empMean z h := by
    intro h hh z
    unfold WassFSG.Lip.empMean
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hG_bd h hh (z i)).1)
  have hempMean_le : ∀ h ∈ G, ∀ z : Fin n → Z, WassFSG.Lip.empMean z h ≤ M := by
    intro h hh z
    unfold WassFSG.Lip.empMean
    have : ∑ i, h (z i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => (hG_bd h hh (z i)).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc 1 / (n : ℝ) * ∑ i, h (z i) ≤ 1 / (n : ℝ) * (n * M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = M := by field_simp
  -- the uniform deviation over G
  set D : (Fin n → Z) → EReal := fun z =>
    ⨆ h ∈ G, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal) with hDdef
  have hD_le : ∀ z, D z ≤ ((1 : ℝ) : EReal) := by
    intro z
    refine iSup₂_le fun h hh => ?_
    rw [EReal.coe_le_coe_iff, hG_one h hh]
    linarith [hempMean_nonneg h hh z]
  have hD_ge : ∀ z, ((1 - WassFSG.Lip.empMean z (g f0) : ℝ) : EReal) ≤ D z := by
    intro z
    have := le_iSup₂ (f := fun h (_ : h ∈ G) =>
      ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal)) (g f0) (hgG f0 hf0)
    have h' : ((∫ x, g f0 x ∂Ptrue - WassFSG.Lip.empMean z (g f0) : ℝ) : EReal) ≤ D z := this
    rw [hg_one f0 hf0] at h'
    exact h'
  set Φ : (Fin n → Z) → ℝ := fun z => (D z).toReal with hΦdef
  have hDΦ : ∀ z, D z = ((Φ z : ℝ) : EReal) := by
    intro z
    have h1 : D z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hD_le z)
    have h2 : D z ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hD_ge z)
    exact (EReal.coe_toReal h1 h2).symm
  have hΦ_term : ∀ h ∈ G, ∀ z, ∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h ≤ Φ z := by
    intro h hh z
    have := le_iSup₂ (f := fun h (_ : h ∈ G) =>
      ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal)) h hh
    have h' : ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal) ≤ D z := this
    rw [hDΦ z] at h'
    exact_mod_cast h'
  have hΦ_sup : ∀ z (c : ℝ), (∀ h ∈ G, ∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h ≤ c) →
      Φ z ≤ c := by
    intro z c hc
    have : D z ≤ (c : EReal) := iSup₂_le fun h hh => EReal.coe_le_coe_iff.mpr (hc h hh)
    rw [hDΦ z] at this
    exact_mod_cast this
  have hΦ_le : ∀ z, Φ z ≤ 1 := by
    intro z
    have := hD_le z
    rw [hDΦ z] at this
    exact_mod_cast this
  have hΦ_ge : ∀ z, 1 - WassFSG.Lip.empMean z (g f0) ≤ Φ z := by
    intro z
    have := hD_ge z
    rw [hDΦ z] at this
    exact_mod_cast this
  -- measurability via lower semicontinuity
  have hD_meas : Measurable D := by
    apply LowerSemicontinuous.measurable
    apply lowerSemicontinuous_biSup
    intro h hh
    apply Continuous.lowerSemicontinuous
    apply continuous_coe_real_ereal.comp
    unfold WassFSG.Lip.empMean
    exact continuous_const.sub (continuous_const.mul
      (continuous_finset_sum _ fun i _ => (hG_cont h hh).comp (continuous_apply i)))
  have hΦ_meas : Measurable Φ := hD_meas.ereal_toReal
  have hΦ_int : Integrable Φ μn := by
    refine Integrable.of_bound hΦ_meas.aestronglyMeasurable (1 + M)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have := hΦ_ge z
    have := hempMean_le (g f0) (hgG f0 hf0) z
    constructor <;> linarith [hΦ_le z]
  -- Lemma 7 (symmetrization)
  have h7 := lemma_7 Ptrue n hn G hG_cont hG_int
  have hEΦ_le : ∫ z, Φ z ∂μn ≤ 2 * RG := by
    have e : ModelRiskOT.Duality.extIntegral μn D = ((∫ z, Φ z ∂μn : ℝ) : EReal) := by
      have : D = fun z => ((Φ z : ℝ) : EReal) := funext hDΦ
      rw [this]
      exact WassFSGCor6Aux.extIntegral_coe μn Φ hΦ_int
    have h7' : ModelRiskOT.Duality.extIntegral μn D ≤ 2 * WassFSG.Lip.expectedRad Ptrue n G := h7
    rw [e, hRG, show (2 : EReal) * (RG : EReal) = ((2 * RG : ℝ) : EReal) by
      rw [EReal.coe_mul]; rfl] at h7'
    exact EReal.coe_le_coe_iff.mp h7'
  -- E Φ ≥ 0
  have hEΦ_ge : 0 ≤ ∫ z, Φ z ∂μn := by
    have hcomp : ∀ i : Fin n, Integrable (fun z : Fin n → Z => g f0 (z i)) μn := by
      intro i
      refine Integrable.of_bound
        ((hg_cont f0 hf0).comp (continuous_apply i)).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_bd f0 hf0 _).1]
      exact (hg_bd f0 hf0 _).2
    have hEmp : ∫ z, WassFSG.Lip.empMean z (g f0) ∂μn = 1 := by
      unfold WassFSG.Lip.empMean
      rw [integral_const_mul, integral_finset_sum _ fun i _ => hcomp i]
      have : ∀ i : Fin n, ∫ z, g f0 (z i) ∂μn = 1 := by
        intro i
        rw [hμn, integral_comp_eval (hg_cont f0 hf0).aestronglyMeasurable]
        exact hg_one f0 hf0
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      field_simp
    have hint1 : Integrable (fun z => 1 - WassFSG.Lip.empMean z (g f0)) μn := by
      unfold WassFSG.Lip.empMean
      exact (integrable_const 1).sub ((integrable_finset_sum _ fun i _ => hcomp i).const_mul _)
    have := integral_mono hint1 hΦ_int hΦ_ge
    rw [integral_sub (integrable_const 1) (by
      unfold WassFSG.Lip.empMean
      exact (integrable_finset_sum _ fun i _ => hcomp i).const_mul _), hEmp] at this
    simpa using this
  have hRGnn : 0 ≤ RG := by linarith
  -- McDiarmid
  have hspos : 0 < s := by
    have : 0 < t / (2 * n) := by positivity
    positivity
  have hbd : ∀ (i : Fin n) (x : Fin n → Z) (a : Z),
      |Φ x - Φ (Function.update x i a)| ≤ M / n := by
    intro i x a
    have key : ∀ x y : Fin n → Z, (∀ h ∈ G, |WassFSG.Lip.empMean x h -
        WassFSG.Lip.empMean y h| ≤ M / n) → Φ x ≤ Φ y + M / n := by
      intro x y hxy
      apply hΦ_sup
      intro h hh
      have h1 := hΦ_term h hh y
      have h2 := (abs_le.mp (hxy h hh)).1
      linarith
    have hxy : ∀ h ∈ G, |WassFSG.Lip.empMean x h -
        WassFSG.Lip.empMean (Function.update x i a) h| ≤ M / n :=
      fun h hh => WassFSGCor6Aux.empMean_update_le hn h M (hG_bd h hh) x i a
    rw [abs_le]
    constructor
    · have := key (Function.update x i a) x (fun h hh => by rw [abs_sub_comm]; exact hxy h hh)
      linarith
    · have := key x (Function.update x i a) hxy
      linarith
  have hmc := RadGauss.RiskBound.mcdiarmid_inequality n (fun _ => Ptrue) Φ hΦ_meas
    (fun _ => M / n) hbd s hspos
  have hexp : -2 * s ^ 2 / ∑ _i : Fin n, (M / n) ^ 2 = -t := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs2 : s ^ 2 = M ^ 2 * (t / (2 * n)) := by
      rw [hsdef, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hs2]
    field_simp
  rw [hexp] at hmc
  -- Theorem 3
  have h3 := theorem_3 Ptrue τ hT F ħ hF hpos γ₂ hγ₂ hbound n hn ψ h5 rstar hrstar hfix t ht
    RG hRG
  -- inclusion of the bad event
  set A := {z : Fin n → Z | ∃ f ∈ F, ¬ (∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
          + rhoN ħ τ t RG rstar n * gradNorm Ptrue f
          + 4 * rstar + 2 * epsN ħ τ t RG n)} with hA
  set B := {x : Fin n → Z | s ≤ Φ x - ∫ y, Φ y ∂μn} with hB
  have hrhoN : 0 ≤ rhoN ħ τ t RG rstar n := by
    unfold rhoN
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (by linarith)) (Real.sqrt_nonneg _)
  set δ : ℝ := 2 * RG + s with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 2 := hsmall
  have hrhoT : rhoTilde ħ τ t RG rstar κg n = rhoN ħ τ t RG rstar n * (1 + δ) := by
    unfold rhoTilde; rw [hδ, hsdef]; ring
  have hrhoT0 : 0 ≤ rhoTilde ħ τ t RG rstar κg n := by
    rw [hrhoT]; exact mul_nonneg hrhoN (by linarith)
  have hsub : {z | ∃ f ∈ F, ¬ ((∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
              + rhoTilde ħ τ t RG rstar κg n * empGradNorm z f
              + 4 * rstar + 2 * epsN ħ τ t RG n) ∧
            (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤ (WassFSG.Lip.empMean z f : EReal)
              + regularizer (WassFSG.Lip.empMeasure z) (rhoTilde ħ τ t RG rstar κg n) f
              + ((4 * rstar + 2 * epsN ħ τ t RG n
                  + ħ * rhoTilde ħ τ t RG rstar κg n ^ 2 : ℝ) : EReal)))} ⊆ A ∪ B := by
    intro z hz
    obtain ⟨f, hf, hbad⟩ := hz
    by_cases hzA : z ∈ A
    · exact Or.inl hzA
    by_cases hzB : z ∈ B
    · exact Or.inr hzB
    exfalso
    apply hbad
    have h3f : ∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
          + rhoN ħ τ t RG rstar n * gradNorm Ptrue f
          + 4 * rstar + 2 * epsN ħ τ t RG n := by
      by_contra hc
      exact hzA ⟨f, hf, hc⟩
    have hΦz : Φ z < δ := by
      have : ¬ (s ≤ Φ z - ∫ y, Φ y ∂μn) := hzB
      rw [hδ]; linarith
    set e := empGradNorm z f with he
    set gn := gradNorm Ptrue f with hgn
    have hgnpos : 0 < gn := hpos f hf
    have he0 : 0 ≤ e := Real.sqrt_nonneg _
    have hemp : WassFSG.Lip.empMean z (g f) = e ^ 2 / gn ^ 2 := by
      rw [he]
      unfold empGradNorm WassFSG.Lip.empMean
      rw [Real.sq_sqrt (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => by positivity))]
      simp only [hgdef]
      rw [← Finset.sum_div]
      ring
    have hdev : 1 - e ^ 2 / gn ^ 2 < δ := by
      have := hΦ_term (g f) (hgG f hf) z
      rw [hg_one f hf, hemp] at this
      linarith
    have hgn_le : gn ≤ e * (1 + δ) :=
      WassFSGCor6Aux.le_mul_one_add_of_dev gn e δ hgnpos he0 hδ0 hδ1 hdev
    have hfirst : ∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f
          + rhoTilde ħ τ t RG rstar κg n * e
          + 4 * rstar + 2 * epsN ħ τ t RG n := by
      have : rhoN ħ τ t RG rstar n * gn ≤ rhoTilde ħ τ t RG rstar κg n * e := by
        rw [hrhoT]
        have := mul_le_mul_of_nonneg_left hgn_le hrhoN
        linarith
      linarith
    refine ⟨hfirst, ?_⟩
    have hf1 : GradLipBound ħ {f} := by
      refine ⟨hF.1, fun f' hf' => ?_⟩
      rw [Set.mem_singleton_iff] at hf'
      rw [hf']
      exact hF.2 f hf
    have h2 := (lemma_2 (WassFSG.Lip.empMeasure z) (WassFSGCor6Aux.isP2_empMeasure hn z)
      (rhoTilde ħ τ t RG rstar κg n) hrhoT0 f ħ hf1).2
    rw [WassFSGCor6Aux.gradNorm_empMeasure hn z f, ← he] at h2
    set ρ := rhoTilde ħ τ t RG rstar κg n
    set C := 4 * rstar + 2 * epsN ħ τ t RG n
    calc (((∫ x, f x ∂Ptrue : ℝ) : EReal))
        ≤ (((WassFSG.Lip.empMean z f + (ρ * e - ħ * ρ ^ 2)) + (C + ħ * ρ ^ 2) : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff]; linarith
      _ = (WassFSG.Lip.empMean z f : EReal) + ((ρ * e - ħ * ρ ^ 2 : ℝ) : EReal)
            + ((C + ħ * ρ ^ 2 : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_add]
      _ ≤ (WassFSG.Lip.empMean z f : EReal) + regularizer (WassFSG.Lip.empMeasure z) ρ f
            + ((C + ħ * ρ ^ 2 : ℝ) : EReal) := by
          gcongr
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le A B) ?_)
  have hsum : ENNReal.ofReal ((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) * Real.exp (-t))
      + ENNReal.ofReal (Real.exp (-t))
      = ENNReal.ofReal (((WassFSG.Lip.peelCount γ₂ τ t n : ℝ) + 1) * Real.exp (-t)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [← hsum]
  exact add_le_add h3 hmc
