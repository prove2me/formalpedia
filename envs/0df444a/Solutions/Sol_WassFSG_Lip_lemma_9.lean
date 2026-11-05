-- Prove2me | solution 1 for WassFSG.Lip.lemma_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:07:52.746261+00:00
-- url     : https://prove2.me/submissions/a36a523f-a6b7-4b13-b4c0-1e6b37c0011b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher
import Theorems.Thm_WassFSG_Conc_lemma_5
import Theorems.Thm_WassFSG_Lip_lemma_7

open MeasureTheory

namespace WassFSGL9Aux

set_option linter.unusedSectionVars false

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

lemma absLip (f : Z → ℝ) (γ₁ : ℝ) (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (z z' : Z) :
    |f z' - f z| ≤ γ₁ * ‖z' - z‖ := by
  rw [_root_.abs_le]
  refine ⟨?_, hf z z'⟩
  have := hf z' z
  rw [norm_sub_rev] at this
  linarith

lemma cont_of (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) : Continuous f := by
  have : LipschitzWith ⟨γ₁, hγ.le⟩ f := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    exact absLip f γ₁ hf y x
  exact this.continuous

lemma integrable_norm_of_P1 (P : Measure Z) (hP : WassFSG.Lip.IsP1 P) :
    Integrable (fun z : Z => ‖z‖) P := by
  refine ⟨continuous_norm.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm_norm]
  exact hP.2

lemma integrable_of_P1 (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) (P : Measure Z) (hP : WassFSG.Lip.IsP1 P) :
    Integrable f P := by
  have := hP.1
  have hcont := cont_of f γ₁ hγ hf
  have hnorm := integrable_norm_of_P1 P hP
  refine Integrable.mono' ((integrable_const |f 0|).add (hnorm.const_mul γ₁))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  have := absLip f γ₁ hf 0 z
  rw [sub_zero] at this
  rw [Real.norm_eq_abs]
  have h2 : |f z| ≤ |f 0| + |f z - f 0| := by
    have := abs_add_le (f 0) (f z - f 0); simpa using this
  simp only [Pi.add_apply]
  linarith

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

/-- A real supremum, shifted by `K`, lies below an extended real `y` as soon as every
shifted term does. -/
lemma ciSup_sub_coe_le {ι : Type*} [Nonempty ι] (b : ι → ℝ) (K : ℝ) (y : EReal)
    (h : ∀ i, ((b i - K : ℝ) : EReal) ≤ y) : (((⨆ i, b i) - K : ℝ) : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact absurd (h i) (by rw [le_bot_iff]; exact EReal.coe_ne_bot _)
  | top => exact le_top
  | coe y =>
    have h' : ∀ i, b i ≤ y + K := fun i => by
      have := EReal.coe_le_coe_iff.1 (h i); linarith
    have := ciSup_le h'
    exact EReal.coe_le_coe_iff.2 (by linarith)

/-- `T₁(τ)` in the `Lip` setting is `T_p(τ)` of the concentration module with `p = 1`. -/
lemma Tp_one_of_T1 (τ : ℝ) (P : Measure Z) (hT : WassFSG.Lip.IsT1 τ P) :
    WassFSG.Conc.Tp 1 τ P := by
  obtain ⟨_, ⟨hP1, hP2⟩, hQ⟩ := hT
  have hc : (WassFSG.Conc.costP (Z := Z) 1) = fun u w => ‖u - w‖ₑ := by
    funext u w; simp [WassFSG.Conc.costP]
  have hm : (WassFSG.Conc.momentP (Z := Z) 1) = fun z => ‖z‖ₑ := by
    funext z; simp [WassFSG.Conc.momentP]
  refine ⟨⟨hP1, by rw [hm]; exact hP2⟩, fun Q ⟨hQ1, hQ2⟩ => ?_⟩
  rw [hc]
  rw [hm] at hQ2
  exact hQ Q ⟨hQ1, hQ2⟩

end WassFSGL9Aux

open WassFSGL9Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : WassFSG.Lip.IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : WassFSG.Lip.LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ)
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal) + WassFSG.Lip.productRegularizer Ptrue n
            (Real.sqrt (τ * t / n)) (WassFSG.Lip.negClass F)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  -- the empty class is trivial
  rcases Set.eq_empty_or_nonempty F with hFe | ⟨f0, hf0⟩
  · subst hFe; simp
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  have hγ := hF.1
  have hP1 : WassFSG.Lip.IsP1 Ptrue := hT.2.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set μ := Measure.pi fun _ : Fin n => Ptrue with hμ
  set ρ := Real.sqrt (τ * t / n) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set m1 := ∫ x, ‖x‖ ∂Ptrue with hm1
  -- the deviation `a f z = E_{P_true}[f] - E_{P_n}[f]` and its supremum `S`
  let a : (Z → ℝ) → (Fin n → Z) → ℝ := fun f z => ∫ x, f x ∂Ptrue - WassFSG.Lip.empMean z f
  let U : (Fin n → Z) → ℝ := fun z => γ₁ * m1 + γ₁ * ((1 / (n : ℝ)) * ∑ i, ‖z i‖)
  have hfint : ∀ f ∈ F, Integrable f Ptrue := fun f hf =>
    integrable_of_P1 f γ₁ hγ (hF.2 f hf) Ptrue hP1
  have hnormint := integrable_norm_of_P1 Ptrue hP1
  -- uniform upper bound on the deviations
  have haU : ∀ f ∈ F, ∀ z, a f z ≤ U z := by
    intro f hf z
    have hi : ∀ i, ∫ x, f x ∂Ptrue - f (z i) ≤ γ₁ * m1 + γ₁ * ‖z i‖ := by
      intro i
      have h1 : ∫ x, f x ∂Ptrue - f (z i) = ∫ x, (f x - f (z i)) ∂Ptrue := by
        rw [integral_sub (hfint f hf) (integrable_const _)]; simp
      rw [h1]
      have h2 : ∫ x, (f x - f (z i)) ∂Ptrue ≤ ∫ x, (γ₁ * ‖x‖ + γ₁ * ‖z i‖) ∂Ptrue := by
        refine integral_mono ((hfint f hf).sub (integrable_const _))
          ((hnormint.const_mul γ₁).add (integrable_const _)) (fun x => ?_)
        have := hF.2 f hf (z i) x
        have h3 : ‖x - z i‖ ≤ ‖x‖ + ‖z i‖ := norm_sub_le _ _
        simp only
        nlinarith
      rw [integral_add (hnormint.const_mul γ₁) (integrable_const _), integral_const_mul] at h2
      simpa using h2
    have hsum : ∑ i, (∫ x, f x ∂Ptrue - f (z i)) ≤ ∑ i, (γ₁ * m1 + γ₁ * ‖z i‖) :=
      Finset.sum_le_sum (fun i _ => hi i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    show ∫ x, f x ∂Ptrue - (1 / (n : ℝ)) * ∑ i, f (z i) ≤
      γ₁ * m1 + γ₁ * ((1 / (n : ℝ)) * ∑ i, ‖z i‖)
    have e1 : ∫ x, f x ∂Ptrue - (1 / (n : ℝ)) * ∑ i, f (z i) =
        (1 / (n : ℝ)) * ((n : ℝ) * ∫ x, f x ∂Ptrue - ∑ i, f (z i)) := by
      field_simp
    have e2 : γ₁ * m1 + γ₁ * ((1 / (n : ℝ)) * ∑ i, ‖z i‖) =
        (1 / (n : ℝ)) * ((n : ℝ) * (γ₁ * m1) + γ₁ * ∑ i, ‖z i‖) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hbdd : ∀ z, BddAbove (Set.range fun f : F => a f z) := fun z =>
    ⟨U z, by rintro _ ⟨⟨f, hf⟩, rfl⟩; exact haU f hf z⟩
  let S : (Fin n → Z) → ℝ := fun z => ⨆ f : F, a f z
  have hle_S : ∀ f ∈ F, ∀ z, a f z ≤ S z := fun f hf z => le_ciSup (hbdd z) ⟨f, hf⟩
  have hS_U : ∀ z, S z ≤ U z := fun z => ciSup_le (fun f => haU f.1 f.2 z)
  -- continuity of each deviation, hence lower semicontinuity and measurability of `S`
  have hacont : ∀ f ∈ F, Continuous (a f) := by
    intro f hf
    have hc := cont_of f γ₁ hγ (hF.2 f hf)
    show Continuous (fun z : Fin n → Z => ∫ x, f x ∂Ptrue - (1 / (n : ℝ)) * ∑ i, f (z i))
    fun_prop
  have hSlsc : LowerSemicontinuous S :=
    lowerSemicontinuous_ciSup hbdd (fun f => (hacont f.1 f.2).lowerSemicontinuous)
  have hSm : Measurable S := hSlsc.measurable
  -- integrability of `S`
  have hevalint : ∀ g : Z → ℝ, Integrable g Ptrue → Integrable
      (fun z : Fin n → Z => (1 / (n : ℝ)) * ∑ i, g (z i)) μ := by
    intro g hg
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun i _ => integrable_comp_eval (i := i) hg)
  have hLint : Integrable (a f0) μ := by
    have := (integrable_const (μ := μ) (∫ x, f0 x ∂Ptrue)).sub (hevalint f0 (hfint f0 hf0))
    exact this
  have hUint : Integrable U μ :=
    (integrable_const _).add ((hevalint _ hnormint).const_mul γ₁)
  have hSint : Integrable S μ := by
    refine Integrable.mono' (hLint.abs.add hUint.abs) hSm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    have h1 := hle_S f0 hf0 z
    have h2 := hS_U z
    rw [Real.norm_eq_abs, Pi.add_apply, abs_le]
    constructor
    · have := neg_abs_le (a f0 z); have := abs_nonneg (U z); linarith
    · have := le_abs_self (U z); have := abs_nonneg (a f0 z); linarith
  set ES := ∫ z, S z ∂μ with hES
  -- the centred function `Φ = S - E_⊗[S]`
  let Φ : (Fin n → Z) → ℝ := fun z => S z - ES
  have hΦm : Measurable Φ := hSm.sub_const _
  have hΦint : Integrable Φ μ := hSint.sub (integrable_const _)
  have hΦ0 : ∫ z, Φ z ∂μ = 0 := by
    show ∫ z, (S z - ES) ∂μ = 0
    rw [integral_sub hSint (integrable_const _)]
    simp [hES]
  set M := |γ₁ * m1 - ES| + 1 with hM
  have hMpos : 0 < M := by positivity
  have hgrowth : ∀ zt : Fin n → Z,
      Φ zt ≤ M + (γ₁ / (n : ℝ)) * WassFSG.Conc.dpPow 1 zt 0 := by
    intro zt
    have h1 := hS_U zt
    have hdp : WassFSG.Conc.dpPow 1 zt 0 = ∑ i, ‖zt i‖ := by
      simp [WassFSG.Conc.dpPow]
    rw [hdp]
    have := le_abs_self (γ₁ * m1 - ES)
    show S zt - ES ≤ M + γ₁ / (n : ℝ) * ∑ i, ‖zt i‖
    have e : γ₁ * ((1 / (n : ℝ)) * ∑ i, ‖zt i‖) = γ₁ / (n : ℝ) * ∑ i, ‖zt i‖ := by ring
    simp only [U] at h1
    linarith
  -- concentration (Lemma 5 with p = 1)
  have hconc := (WassFSG.Conc.lemma_5 n hn 1 τ le_rfl (by norm_num) hT.1 Ptrue
    (Tp_one_of_T1 τ Ptrue hT) Φ hΦm hΦint hΦ0 M γ₁ hMpos hγ 0 hgrowth).2 t ht
  -- symmetrization (Lemma 7)
  have hsym := WassFSG.Lip.lemma_7 Ptrue n hn F
    (fun h hh => cont_of h γ₁ hγ (hF.2 h hh)) hfint
  have hsupeq : (fun z => ⨆ h ∈ F, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal))
      = fun z => ((S z : ℝ) : EReal) := by
    funext z
    refine le_antisymm (iSup₂_le (fun h hh => EReal.coe_le_coe_iff.2 (hle_S h hh z))) ?_
    have := ciSup_sub_coe_le (fun f : F => a f z) 0
      (⨆ h ∈ F, ((∫ x, h x ∂Ptrue - WassFSG.Lip.empMean z h : ℝ) : EReal))
      (fun f => by
        simp only [sub_zero]
        exact le_iSup₂_of_le (f : Z → ℝ) f.2 le_rfl)
    simpa using this
  rw [hsupeq, extIntegral_eq μ S hSint] at hsym
  -- the main inclusion
  refine le_trans (measure_mono ?_) hconc
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨f, hf, hbad⟩ := hz
  intro hgood
  apply hbad
  -- Step 1: `Φ z ≤ R_{⊗,1}(ρ; -F)`
  have hR : ((WassFSG.Conc.calR n 1 Ptrue Φ ρ : ENNReal) : EReal) ≤
      WassFSG.Lip.productRegularizer Ptrue n ρ (WassFSG.Lip.negClass F) := by
    unfold WassFSG.Lip.productRegularizer
    refine le_iInf₂ (fun lam hlam => ?_)
    set G : (Fin n → Z) → EReal := fun z => ⨆ g ∈ WassFSG.Lip.negClass F, ⨆ z' : Fin n → Z,
      (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - lam * ‖z' i - z i‖) : ℝ) : EReal) with hG
    have hG0 : ∀ z, 0 ≤ G z := by
      intro z
      refine le_iSup₂_of_le (-f0) ⟨f0, hf0, rfl⟩ (le_iSup_of_le z ?_)
      simp
    have hext : ModelRiskOT.Duality.extIntegral μ G = ((∫⁻ z, (G z).toENNReal ∂μ : ENNReal) : EReal) := by
      unfold ModelRiskOT.Duality.extIntegral
      have : (fun z => (-G z).toENNReal) = fun _ => 0 := by
        funext z; exact EReal.toENNReal_of_nonpos (by simpa using hG0 z)
      rw [this, lintegral_zero]
      simp
    rw [hext]
    have hstep : WassFSG.Conc.calR n 1 Ptrue Φ ρ ≤ ENNReal.ofReal (lam * ρ) +
        ∫⁻ z, (G z).toENNReal ∂μ := by
      unfold WassFSG.Conc.calR
      refine le_trans (iInf₂_le lam hlam) ?_
      rw [Real.rpow_one]
      gcongr with z
      refine iSup_le (fun zt => ?_)
      rw [← EReal.real_coe_toENNReal]
      refine EReal.toENNReal_le_toENNReal ?_
      -- `Φ zt - Φ z - (λ/n) d₁(zt, z) ≤ G z`
      have hdp : WassFSG.Conc.dpPow 1 zt z = ∑ i, ‖zt i - z i‖ := by
        simp [WassFSG.Conc.dpPow]
      rw [hdp]
      have hrw : Φ zt - Φ z - lam / (n : ℝ) * ∑ i, ‖zt i - z i‖ =
          (⨆ f : F, a f zt) - (S z + lam / (n : ℝ) * ∑ i, ‖zt i - z i‖) := by
        show S zt - ES - (S z - ES) - _ = _
        ring
      rw [hrw]
      refine ciSup_sub_coe_le (fun f : F => a f zt) _ (G z) (fun g => ?_)
      have h1 := hle_S g.1 g.2 z
      have hcalc : a g zt - (S z + lam / (n : ℝ) * ∑ i, ‖zt i - z i‖) ≤
          (1 / (n : ℝ)) * ∑ i, ((-(g : Z → ℝ)) (zt i) - (-(g : Z → ℝ)) (z i)
            - lam * ‖zt i - z i‖) := by
        have e : (1 / (n : ℝ)) * ∑ i, ((-(g : Z → ℝ)) (zt i) - (-(g : Z → ℝ)) (z i)
            - lam * ‖zt i - z i‖) = a g zt - a g z - lam / (n : ℝ) * ∑ i, ‖zt i - z i‖ := by
          simp only [a, WassFSG.Lip.empMean, Pi.neg_apply, Finset.sum_sub_distrib,
            Finset.sum_neg_distrib, ← Finset.mul_sum]
          ring
        rw [e]
        linarith
      refine le_trans (EReal.coe_le_coe_iff.2 hcalc) ?_
      exact le_iSup₂_of_le (-(g : Z → ℝ)) ⟨g.1, g.2, rfl⟩ (le_iSup_of_le zt le_rfl)
    calc ((WassFSG.Conc.calR n 1 Ptrue Φ ρ : ENNReal) : EReal)
        ≤ ((ENNReal.ofReal (lam * ρ) + ∫⁻ z, (G z).toENNReal ∂μ : ENNReal) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hstep
      _ = ((lam * ρ : ℝ) : EReal) + ((∫⁻ z, (G z).toENNReal ∂μ : ENNReal) : EReal) := by
          rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal,
            max_eq_left (mul_nonneg hlam hρ0)]
  have hΦle : ((Φ z : ℝ) : EReal) ≤
      WassFSG.Lip.productRegularizer Ptrue n ρ (WassFSG.Lip.negClass F) := by
    refine le_trans ?_ (le_trans (EReal.coe_ennreal_le_coe_ennreal_iff.2 hgood) hR)
    rw [EReal.coe_ennreal_ofReal]
    exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
  -- Step 2: assemble
  have hfS := hle_S f hf z
  have hdecomp : ((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
      (WassFSG.Lip.empMean z f : EReal) + ((Φ z : ℝ) : EReal) + ((ES : ℝ) : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_add]
    refine EReal.coe_le_coe_iff.2 ?_
    show ∫ x, f x ∂Ptrue ≤ WassFSG.Lip.empMean z f + (S z - ES) + ES
    simp only [a] at hfS
    linarith
  refine le_trans hdecomp ?_
  gcongr
