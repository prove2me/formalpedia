-- Prove2me | solution 1 for WassFSG.Lip.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:57:09.693839+00:00
-- url     : https://prove2.me/submissions/d8677248-a4e6-4f51-92e4-cacda83899ee

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting

open MeasureTheory

namespace WassFSGL1Aux

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

lemma absLip (f : Z → ℝ) (γ₁ : ℝ) (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (z z' : Z) :
    |f z' - f z| ≤ γ₁ * ‖z' - z‖ := by
  rw [_root_.abs_le]
  refine ⟨?_, hf z z'⟩
  have := hf z' z
  rw [norm_sub_rev] at this
  linarith

lemma inner_le (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (z z' : Z) :
    (⨆ (_ : z ≠ z'), |f z' - f z| / ‖z' - z‖) ≤ γ₁ := by
  refine Real.iSup_le (fun h => ?_) hγ.le
  have hpos : 0 < ‖z' - z‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
  rw [div_le_iff₀ hpos]
  exact absLip f γ₁ hf z z'

lemma inner2_le (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (z : Z) :
    (⨆ (z' : Z) (_ : z ≠ z'), |f z' - f z| / ‖z' - z‖) ≤ γ₁ :=
  Real.iSup_le (fun z' => inner_le f γ₁ hγ hf z z') hγ.le

lemma lipNorm_nonneg (f : Z → ℝ) : 0 ≤ WassFSG.Conc.lipNorm f := by
  unfold WassFSG.Conc.lipNorm
  refine Real.iSup_nonneg (fun z => Real.iSup_nonneg (fun z' => Real.iSup_nonneg (fun _ => ?_)))
  positivity

lemma le_lipNorm (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (z z' : Z) :
    f z' - f z ≤ WassFSG.Conc.lipNorm f * ‖z' - z‖ := by
  by_cases h : z = z'
  · subst h; simp
  have hpos : 0 < ‖z' - z‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
  have h1 : |f z' - f z| / ‖z' - z‖ ≤ WassFSG.Conc.lipNorm f := by
    unfold WassFSG.Conc.lipNorm
    have hb1 : BddAbove (Set.range fun z : Z => ⨆ (z' : Z) (_ : z ≠ z'), |f z' - f z| / ‖z' - z‖) :=
      ⟨γ₁, by rintro _ ⟨w, rfl⟩; exact inner2_le f γ₁ hγ hf w⟩
    have hb2 : BddAbove (Set.range fun z' : Z => ⨆ (_ : z ≠ z'), |f z' - f z| / ‖z' - z‖) :=
      ⟨γ₁, by rintro _ ⟨w, rfl⟩; exact inner_le f γ₁ hγ hf z w⟩
    refine le_trans ?_ (le_ciSup hb1 z)
    refine le_trans ?_ (le_ciSup hb2 z')
    rw [ciSup_pos h]
  rw [div_le_iff₀ hpos] at h1
  exact le_trans (le_abs_self _) h1

/-- A Lipschitz function is integrable against a measure in `P₁`. -/
lemma integrable_of_P1 (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (P : Measure Z) (hP : WassFSG.Lip.IsP1 P) :
    Integrable f P := by
  haveI := hP.1
  have hcont : Continuous f := by
    have : LipschitzWith ⟨γ₁, hγ.le⟩ f := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      rw [Real.dist_eq, dist_eq_norm]
      exact absLip f γ₁ hf y x
    exact this.continuous
  have hnorm : Integrable (fun z : Z => ‖z‖) P := by
    refine ⟨continuous_norm.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, enorm_norm]
    exact hP.2
  refine Integrable.mono' ((integrable_const |f 0|).add (hnorm.const_mul γ₁))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  have := absLip f γ₁ hf 0 z
  rw [sub_zero] at this
  rw [Real.norm_eq_abs]
  have h2 : |f z| ≤ |f 0| + |f z - f 0| := by
    have := abs_add_le (f 0) (f z - f 0); simpa using this
  simp only [Pi.add_apply]
  linarith

lemma integrable_id_of_P1 (P : Measure Z) (hP : WassFSG.Lip.IsP1 P) :
    Integrable (fun z : Z => z) P := by
  refine ⟨aestronglyMeasurable_id, ?_⟩
  simpa [HasFiniteIntegral] using hP.2

/-- The extended integral of an integrable real function is its Bochner integral. -/
lemma extIntegral_eq {X : Type*} [MeasurableSpace X] (ν : Measure X) (g : X → ℝ)
    (hg : Integrable g ν) :
    ModelRiskOT.Duality.extIntegral ν (fun x => (g x : EReal)) = ((∫ x, g x ∂ν : ℝ) : EReal) := by
  unfold ModelRiskOT.Duality.extIntegral
  have h1 : (fun x => ((g x : EReal)).toENNReal) = fun x => ENNReal.ofReal (g x) := by
    funext x; exact EReal.real_coe_toENNReal _
  have h2 : (fun x => (-(g x : EReal)).toENNReal) = fun x => ENNReal.ofReal (-g x) := by
    funext x; rw [← EReal.coe_neg]; exact EReal.real_coe_toENNReal _
  rw [h1, h2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have hp : ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≠ ⊤ := hg.lintegral_lt_top.ne
  have hn : ∫⁻ x, ENNReal.ofReal (-g x) ∂ν ≠ ⊤ := hg.neg.lintegral_lt_top.ne
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hp, EReal.coe_ennreal_toReal hn]

lemma cont_of (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) : Continuous f := by
  have : LipschitzWith ⟨γ₁, hγ.le⟩ f := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    exact absLip f γ₁ hf y x
  exact this.continuous

/-- Upper bound: transporting at `W₁`-cost `≤ ρ` raises the mean by at most `ρ ‖f‖_Lip`. -/
lemma mean_le (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (P Q : Measure Z)
    (hP : WassFSG.Lip.IsP1 P) (hQ : WassFSG.Lip.IsP1 Q) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hW : WassFSG.Lip.W1 P Q ≤ ENNReal.ofReal ρ) :
    ∫ x, f x ∂P ≤ ∫ x, f x ∂Q + WassFSG.Conc.lipNorm f * ρ := by
  set L := WassFSG.Conc.lipNorm f with hL
  have hL0 : 0 ≤ L := lipNorm_nonneg f
  have hcont := cont_of f γ₁ hγ hf
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  set η := ε / (L + 1) with hη
  have hη0 : 0 < η := by positivity
  have hlt : WassFSG.Lip.W1 P Q < ENNReal.ofReal (ρ + η) :=
    lt_of_le_of_lt hW ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  unfold WassFSG.Lip.W1 RWPI.SqrtLasso.transportCost at hlt
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨⟨hprob, h1, h2⟩, hc⟩ := iInf_lt_iff.1 hπ
  have hfP := integrable_of_P1 f γ₁ hγ hf P hP
  have hfQ := integrable_of_P1 f γ₁ hγ hf Q hQ
  have hiP := integrable_id_of_P1 P hP
  have hiQ := integrable_id_of_P1 Q hQ
  rw [← h1] at hfP hiP
  rw [← h2] at hfQ hiQ
  have hm1 : Integrable (fun u : Z × Z => f u.1) π :=
    (integrable_map_measure hfP.aestronglyMeasurable measurable_fst.aemeasurable).1 hfP
  have hm2 : Integrable (fun u : Z × Z => f u.2) π :=
    (integrable_map_measure hfQ.aestronglyMeasurable measurable_snd.aemeasurable).1 hfQ
  have hi1 : Integrable (fun u : Z × Z => u.1) π :=
    (integrable_map_measure hiP.aestronglyMeasurable measurable_fst.aemeasurable).1 hiP
  have hi2 : Integrable (fun u : Z × Z => u.2) π :=
    (integrable_map_measure hiQ.aestronglyMeasurable measurable_snd.aemeasurable).1 hiQ
  have hd : Integrable (fun u : Z × Z => u.1 - u.2) π := hi1.sub hi2
  have hEP : ∫ x, f x ∂P = ∫ u, f u.1 ∂π := by
    rw [← h1, integral_map measurable_fst.aemeasurable hfP.aestronglyMeasurable]
  have hEQ : ∫ x, f x ∂Q = ∫ u, f u.2 ∂π := by
    rw [← h2, integral_map measurable_snd.aemeasurable hfQ.aestronglyMeasurable]
  set D := ∫ u, ‖u.1 - u.2‖ ∂π with hD
  have hDlt : D < ρ + η := by
    have := ofReal_integral_norm_eq_lintegral_enorm hd
    have hc' : ∫⁻ u, ‖u.1 - u.2‖ₑ ∂π < ENNReal.ofReal (ρ + η) := hc
    rw [← this] at hc'
    exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 hc').1
  have hdiff : ∫ x, f x ∂P - ∫ x, f x ∂Q ≤ L * D := by
    rw [hEP, hEQ, ← integral_sub hm1 hm2, hD, ← integral_const_mul]
    refine integral_mono (hm1.sub hm2) (hd.norm.const_mul L) (fun u => ?_)
    exact le_lipNorm f γ₁ hγ hf u.2 u.1
  have h3 : L * D ≤ L * (ρ + η) := mul_le_mul_of_nonneg_left hDlt.le hL0
  have h4 : L * η < ε := by
    rw [hη, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  nlinarith

lemma dirac_P1 (z : Z) : WassFSG.Lip.IsP1 (Measure.dirac z) := by
  refine ⟨inferInstance, ?_⟩
  rw [lintegral_dirac]
  exact enorm_lt_top

lemma mix_P1 (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q) (z : Z) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    WassFSG.Lip.IsP1 (ENNReal.ofReal (1 - p) • Q + ENNReal.ofReal p • Measure.dirac z) := by
  haveI := hQ.1
  refine ⟨⟨?_⟩, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hp0]
    simp
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQ.2,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top⟩

lemma W1_self (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q) : WassFSG.Lip.W1 Q Q = 0 := by
  haveI := hQ.1
  refine le_antisymm ?_ bot_le
  have hm : Measurable (fun x : Z => (x, x)) := measurable_id.prodMk measurable_id
  unfold WassFSG.Lip.W1 RWPI.SqrtLasso.transportCost
  refine iInf₂_le_of_le (Q.map (fun x => (x, x)))
    ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩ ?_
  · rw [Measure.map_map measurable_fst hm]; exact Measure.map_id
  · rw [Measure.map_map measurable_snd hm]; exact Measure.map_id
  · beta_reduce
    rw [lintegral_map (by fun_prop) hm]
    simp

lemma mix_W1 (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q) (z : Z) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    WassFSG.Lip.W1 (ENNReal.ofReal (1 - p) • Q + ENNReal.ofReal p • Measure.dirac z) Q
      ≤ ENNReal.ofReal p * ∫⁻ w, ‖z - w‖ₑ ∂Q := by
  haveI := hQ.1
  have hm : Measurable (fun x : Z => (x, x)) := measurable_id.prodMk measurable_id
  have hm' : Measurable (fun w : Z => (z, w)) := measurable_const.prodMk measurable_id
  unfold WassFSG.Lip.W1 RWPI.SqrtLasso.transportCost
  refine iInf₂_le_of_le (ENNReal.ofReal (1 - p) • Q.map (fun x => (x, x)) +
      ENNReal.ofReal p • Q.map (fun w => (z, w))) ⟨⟨?_⟩, ?_, ?_⟩ ?_
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hm MeasurableSet.univ, Measure.map_apply hm' MeasurableSet.univ,
      Set.preimage_univ, Set.preimage_univ, measure_univ, mul_one, mul_one,
      ← ENNReal.ofReal_add (by linarith) hp0]
    simp
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_fst hm, Measure.map_map measurable_fst hm']
    have e1 : (Prod.fst ∘ fun x : Z => (x, x)) = id := rfl
    have e2 : (Prod.fst ∘ fun w : Z => (z, w)) = fun _ => z := rfl
    rw [e1, e2, Measure.map_id, Measure.map_const, measure_univ, one_smul]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      Measure.map_map measurable_snd hm, Measure.map_map measurable_snd hm']
    have e1 : (Prod.snd ∘ fun x : Z => (x, x)) = id := rfl
    have e2 : (Prod.snd ∘ fun w : Z => (z, w)) = id := rfl
    rw [e1, e2, Measure.map_id, ← add_smul, ← ENNReal.ofReal_add (by linarith) hp0]
    simp
  · beta_reduce
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_map (by fun_prop) hm, lintegral_map (by fun_prop) hm']
    simp

lemma mix_integral (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q)
    (z : Z) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, f x ∂(ENNReal.ofReal (1 - p) • Q + ENNReal.ofReal p • Measure.dirac z)
      = (1 - p) * ∫ x, f x ∂Q + p * f z := by
  have hfQ := integrable_of_P1 f γ₁ hγ hf Q hQ
  have hfd := integrable_of_P1 f γ₁ hγ hf _ (dirac_P1 z)
  rw [integral_add_measure (hfQ.smul_measure ENNReal.ofReal_ne_top)
    (hfd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0]
  simp [smul_eq_mul]

/-- Lower bound: moving a small mass far out along a direction of maximal slope. -/
lemma exists_good (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z₀ : Z)
    (hlim : Filter.limsup (fun z => (((f z - f z₀) / ‖z - z₀‖ : ℝ) : EReal))
      (Filter.comap (fun z => ‖z - z₀‖) Filter.atTop) = (WassFSG.Conc.lipNorm f : EReal))
    (b : ℝ) (hb : b < ∫ x, f x ∂Q + ρ * WassFSG.Conc.lipNorm f) :
    ∃ P : Measure Z, (WassFSG.Lip.IsP1 P ∧ WassFSG.Lip.W1 P Q ≤ ENNReal.ofReal ρ) ∧
      b ≤ ∫ x, f x ∂P := by
  haveI := hQ.1
  set L := WassFSG.Conc.lipNorm f with hL
  set a := ∫ x, f x ∂Q with ha
  have hL0 : 0 ≤ L := lipNorm_nonneg f
  by_cases hba : b < a
  · exact ⟨Q, ⟨hQ, by rw [W1_self Q hQ]; exact bot_le⟩, hba.le⟩
  push Not at hba
  have hρL : 0 < ρ * L := by linarith
  have hρpos : 0 < ρ := by
    rcases hρ.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hρL; exact absurd hρL (lt_irrefl 0)
  have hLpos : 0 < L := by
    rcases hL0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hρL; exact absurd hρL (lt_irrefl 0)
  set δ := a + ρ * L - b with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := δ / (2 * ρ) with hε
  have hε0 : 0 < ε := by positivity
  have hερ : 2 * ρ * ε = δ := by rw [hε]; field_simp
  have hfreq : ∃ᶠ z in Filter.comap (fun z => ‖z - z₀‖) Filter.atTop,
      ((L - ε : ℝ) : EReal) < (((f z - f z₀) / ‖z - z₀‖ : ℝ) : EReal) :=
    Filter.frequently_lt_of_lt_limsup (by isBoundedDefault)
      (by rw [hlim]; exact_mod_cast (by linarith : L - ε < L))
  rw [Filter.frequently_comap, Filter.frequently_atTop] at hfreq
  have hfQ := integrable_of_P1 f γ₁ hγ hf Q hQ
  have hdz : Integrable (fun w => w - z₀) Q := (integrable_id_of_P1 Q hQ).sub (integrable_const z₀)
  set M := ∫ w, ‖w - z₀‖ ∂Q with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  obtain ⟨r, hr, z, hzr, hz⟩ := hfreq (max (max ρ 1) (4 * ρ * L * M / δ))
  have hr1 : ρ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr2 : (1 : ℝ) ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr3 : 4 * ρ * L * M / δ ≤ r := le_trans (le_max_right _ _) hr
  have hrpos : 0 < r := by linarith
  have hr3' : 4 * ρ * L * M ≤ δ * r := by
    rw [div_le_iff₀ hδ0] at hr3; linarith
  rw [hzr, EReal.coe_lt_coe_iff, lt_div_iff₀ hrpos] at hz
  -- the mixing weight
  set p := ρ / (r + M) with hp
  have hrM : 0 < r + M := by linarith
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hrM]; linarith
  have hpr : p * (r + M) = ρ := by rw [hp]; field_simp
  refine ⟨ENNReal.ofReal (1 - p) • Q + ENNReal.ofReal p • Measure.dirac z,
    ⟨mix_P1 Q hQ z p hp0 hp1, ?_⟩, ?_⟩
  · refine le_trans (mix_W1 Q hQ z p hp0 hp1) ?_
    have hint : ∫⁻ w, ‖z - w‖ₑ ∂Q ≤ ENNReal.ofReal (r + M) := by
      calc ∫⁻ w, ‖z - w‖ₑ ∂Q ≤ ∫⁻ w, (‖z - z₀‖ₑ + ‖w - z₀‖ₑ) ∂Q := by
            refine lintegral_mono (fun w => ?_)
            rw [show z - w = (z - z₀) - (w - z₀) by abel]
            exact enorm_sub_le
        _ = ‖z - z₀‖ₑ + ∫⁻ w, ‖w - z₀‖ₑ ∂Q := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        _ = ENNReal.ofReal (r + M) := by
            rw [← ofReal_integral_norm_eq_lintegral_enorm hdz, ENNReal.ofReal_add hrpos.le hM0,
              ← hzr, ofReal_norm]
    calc ENNReal.ofReal p * ∫⁻ w, ‖z - w‖ₑ ∂Q ≤ ENNReal.ofReal p * ENNReal.ofReal (r + M) :=
          mul_le_mul' le_rfl hint
      _ = ENNReal.ofReal ρ := by rw [← ENNReal.ofReal_mul hp0, hpr]
  · rw [mix_integral f γ₁ hγ hf Q hQ z p hp0 hp1]
    have haQ : a - f z₀ ≤ L * M := by
      have h : ∫ w, (f w - f z₀) ∂Q ≤ ∫ w, L * ‖w - z₀‖ ∂Q :=
        integral_mono (hfQ.sub (integrable_const (f z₀))) (hdz.norm.const_mul L)
          (fun w => le_lipNorm f γ₁ hγ hf z₀ w)
      rw [integral_sub hfQ (integrable_const _), integral_const, integral_const_mul] at h
      simpa using h
    have hfz : (L - ε) * r - L * M ≤ f z - a := by linarith
    have h1 : p * ((L - ε) * r - L * M) ≤ p * (f z - a) := mul_le_mul_of_nonneg_left hfz hp0
    have hpr' : p * r = ρ - p * M := by linarith
    have h2 : 4 * p * L * M ≤ δ := by
      have : 4 * p * L * M * r ≤ δ * r := by
        calc 4 * p * L * M * r ≤ 4 * L * M * (p * (r + M)) := by
              have : 0 ≤ 4 * L * M * (p * M) := by positivity
              nlinarith
          _ = 4 * ρ * L * M := by rw [hpr]; ring
          _ ≤ δ * r := hr3'
      exact le_of_mul_le_mul_right this hrpos
    have h3 : 0 ≤ ε * p * M := by positivity
    have e1 : p * ((L - ε) * r - L * M) = L * ρ - 2 * (p * L * M) - ε * ρ + ε * p * M := by
      have : p * ((L - ε) * r - L * M) = (L - ε) * (p * r) - p * L * M := by ring
      rw [this, hpr']; ring
    have e2 : ε * ρ = δ / 2 := by linarith
    nlinarith

end WassFSGL1Aux

open WassFSGL1Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Q : Measure Z) (hQ : WassFSG.Lip.IsP1 Q) (ρ : ℝ) (hρ : 0 ≤ ρ) (f : Z → ℝ) (γ₁ : ℝ)
    (hf : WassFSG.Lip.LipBound γ₁ {f}) :
    WassFSG.Lip.regularizer Q ρ f ≤ ((ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal) ∧
      (WassFSG.Lip.LipAttainedAtInfinity ({f} : Set (Z → ℝ)) →
        WassFSG.Lip.regularizer Q ρ f = ((ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal)) := by
  have hγ : 0 < γ₁ := hf.1
  have hf' : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖ := hf.2 f rfl
  have hfQ := integrable_of_P1 f γ₁ hγ hf' Q hQ
  set L := WassFSG.Conc.lipNorm f with hL
  set a := ∫ x, f x ∂Q with ha
  set S := ⨆ (P : Measure Z) (_ : WassFSG.Lip.IsP1 P ∧ WassFSG.Lip.W1 P Q ≤ ENNReal.ofReal ρ),
      ModelRiskOT.Duality.extIntegral P (fun z => (f z : EReal)) with hS
  have hreg : WassFSG.Lip.regularizer Q ρ f = S - (a : EReal) := by
    unfold WassFSG.Lip.regularizer
    rw [extIntegral_eq Q f hfQ]
  have hup : S ≤ ((a + ρ * L : ℝ) : EReal) := by
    refine iSup₂_le (fun P hP => ?_)
    rw [extIntegral_eq P f (integrable_of_P1 f γ₁ hγ hf' P hP.1)]
    have := mean_le f γ₁ hγ hf' P Q hP.1 hQ ρ hρ hP.2
    exact_mod_cast (by linarith : ∫ x, f x ∂P ≤ a + ρ * L)
  have part1 : S - (a : EReal) ≤ ((ρ * L : ℝ) : EReal) := by
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a)),
      ← EReal.coe_add, add_comm (ρ * L)]
    exact hup
  refine ⟨hreg ▸ part1, fun hA => ?_⟩
  obtain ⟨z₀, hz₀⟩ := hA.2 f rfl
  rw [hreg]
  refine le_antisymm part1 ?_
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a)),
    ← EReal.coe_add]
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hSb, hb⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  rw [EReal.coe_lt_coe_iff] at hb
  obtain ⟨P, hP, hbP⟩ := exists_good f γ₁ hγ hf' Q hQ ρ hρ z₀ hz₀ b (by linarith)
  have : ((∫ x, f x ∂P : ℝ) : EReal) ≤ S := by
    rw [← extIntegral_eq P f (integrable_of_P1 f γ₁ hγ hf' P hP.1)]
    exact le_iSup₂_of_le P hP le_rfl
  have : (b : EReal) ≤ S := le_trans (by exact_mod_cast hbP) this
  exact absurd hSb (not_lt.2 this)
