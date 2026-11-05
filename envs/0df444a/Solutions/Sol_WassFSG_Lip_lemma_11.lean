-- Prove2me | solution 1 for WassFSG.Lip.lemma_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:09:20.564003+00:00
-- url     : https://prove2.me/submissions/cbbbb6fe-119a-4682-800d-2571f446f7e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher
import Theorems.Thm_WassFSG_Lip_lemma_9

open MeasureTheory

namespace WassFSGL11Aux

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

lemma lipNorm_le (f : Z → ℝ) (γ₁ : ℝ) (hγ : 0 < γ₁)
    (hf : ∀ z z' : Z, f z' - f z ≤ γ₁ * ‖z' - z‖) : WassFSG.Conc.lipNorm f ≤ γ₁ :=
  Real.iSup_le (fun z => inner2_le f γ₁ hγ hf z) hγ.le

end WassFSGL11Aux

open WassFSGL11Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : WassFSG.Lip.IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : WassFSG.Lip.LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ)
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal)
            + ((Real.sqrt (τ * t / n) * ⨆ g : F, WassFSG.Conc.lipNorm (g : Z → ℝ) : ℝ) : EReal)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  have hγ := hF.1
  set ρ := Real.sqrt (τ * t / n) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set L := ⨆ g : F, WassFSG.Conc.lipNorm (g : Z → ℝ) with hL
  have hbdd : BddAbove (Set.range fun g : F => WassFSG.Conc.lipNorm (g : Z → ℝ)) :=
    ⟨γ₁, by rintro _ ⟨g, rfl⟩; exact lipNorm_le g.1 γ₁ hγ (hF.2 g.1 g.2)⟩
  have hfL : ∀ f ∈ F, WassFSG.Conc.lipNorm f ≤ L := fun f hf => le_ciSup hbdd ⟨f, hf⟩
  have hL0 : 0 ≤ L := Real.iSup_nonneg (fun g => lipNorm_nonneg _)
  -- `R_{⊗,1}(ρ; -F) ≤ ρ sup_F ‖f‖_Lip` (take `λ = sup_F ‖f‖_Lip`)
  have hR : WassFSG.Lip.productRegularizer Ptrue n ρ (WassFSG.Lip.negClass F) ≤
      ((ρ * L : ℝ) : EReal) := by
    unfold WassFSG.Lip.productRegularizer
    refine le_trans (iInf₂_le L hL0) ?_
    have hG : ∀ z : Fin n → Z, (⨆ g ∈ WassFSG.Lip.negClass F, ⨆ z' : Fin n → Z,
        (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - L * ‖z' i - z i‖) : ℝ) : EReal)) ≤ 0 := by
      intro z
      refine iSup₂_le (fun g hg => iSup_le (fun z' => ?_))
      obtain ⟨f, hf, rfl⟩ := hg
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
      refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
      refine Finset.sum_nonpos (fun i _ => ?_)
      have h1 := le_lipNorm f γ₁ hγ (hF.2 f hf) (z' i) (z i)
      have h2 := hfL f hf
      have h3 : WassFSG.Conc.lipNorm f * ‖z i - z' i‖ ≤ L * ‖z' i - z i‖ := by
        rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      simp only [Pi.neg_apply]
      linarith
    have hext : ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
        (fun z => ⨆ g ∈ WassFSG.Lip.negClass F, ⨆ z' : Fin n → Z,
          (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - L * ‖z' i - z i‖) : ℝ) : EReal)) ≤ 0 := by
      unfold ModelRiskOT.Duality.extIntegral
      have : (fun z : Fin n → Z => (⨆ g ∈ WassFSG.Lip.negClass F, ⨆ z' : Fin n → Z,
          (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - L * ‖z' i - z i‖) : ℝ) :
            EReal)).toENNReal) = fun _ => 0 := by
        funext z; exact EReal.toENNReal_of_nonpos (hG z)
      rw [this, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]
      have h0 := EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_nonneg (∫⁻ z, (-(⨆ g ∈ WassFSG.Lip.negClass F, ⨆ z' : Fin n → Z,
          (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - L * ‖z' i - z i‖) : ℝ) : EReal))).toENNReal
            ∂(Measure.pi fun _ : Fin n => Ptrue)))
      simpa using h0
    calc ((L * ρ : ℝ) : EReal) + _ ≤ ((L * ρ : ℝ) : EReal) + 0 := by gcongr
      _ = ((ρ * L : ℝ) : EReal) := by rw [add_zero, mul_comm]
  refine le_trans (measure_mono ?_)
    (WassFSG.Lip.lemma_9 Ptrue τ hT F γ₁ hF t ht n hn)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨f, hf, hbad⟩ := hz
  refine ⟨f, hf, fun hgood => hbad (le_trans hgood ?_)⟩
  gcongr
