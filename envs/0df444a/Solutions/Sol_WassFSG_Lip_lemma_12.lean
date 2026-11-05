-- Prove2me | solution 1 for WassFSG.Lip.lemma_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:11:37.750218+00:00
-- url     : https://prove2.me/submissions/e9967c4f-9def-46ab-9856-dff8fe6ac70c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting
import Definitions.Def_WassFSG_Lip_Rademacher
import Theorems.Thm_WassFSG_Lip_lemma_11

open MeasureTheory

namespace WassFSGL12Aux

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

lemma extIntegral_mono {X : Type*} [MeasurableSpace X] (ν : Measure X) (φ ψ : X → EReal)
    (h : ∀ x, φ x ≤ ψ x) :
    ModelRiskOT.Duality.extIntegral ν φ ≤ ModelRiskOT.Duality.extIntegral ν ψ := by
  unfold ModelRiskOT.Duality.extIntegral
  refine EReal.sub_le_sub ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono (fun x => EReal.toENNReal_le_toENNReal (h x)))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
      (lintegral_mono (fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h x))))

lemma expectedRad_mono (P : Measure Z) (n : ℕ) (G G' : Set (Z → ℝ)) (hG : G ⊆ G') :
    WassFSG.Lip.expectedRad P n G ≤ WassFSG.Lip.expectedRad P n G' := by
  unfold WassFSG.Lip.expectedRad
  refine extIntegral_mono _ _ _ (fun z => ?_)
  unfold WassFSG.Lip.radComp
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / 2 ^ n))
  refine Finset.sum_le_sum (fun σ _ => ?_)
  exact biSup_mono (fun g hg => hG hg)

end WassFSGL12Aux

open WassFSGL12Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (Ptrue : Measure Z) [IsProbabilityMeasure Ptrue] (τ : ℝ) (hT : WassFSG.Lip.IsT1 τ Ptrue)
    (F : Set (Z → ℝ)) (γ₁ : ℝ) (hF : WassFSG.Lip.LipBound γ₁ F) (t : ℝ) (ht : 0 < t) (n : ℕ)
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => Ptrue)
        {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          ((WassFSG.Lip.empMean z f + 2 * Real.sqrt (τ * t / n) * WassFSG.Conc.lipNorm f : ℝ) :
            EReal)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F + ((1 / (n : ℝ) : ℝ) : EReal))}
      ≤ ENNReal.ofReal ((WassFSG.Lip.peelCount γ₁ τ t n : ℝ) * Real.exp (-t)) := by
  classical
  have hγ := hF.1
  have hτ := hT.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set ρ := Real.sqrt (τ * t / n) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set K : ℕ := (max 0 ⌈Real.logb 2 (γ₁ * Real.sqrt (τ * t * n))⌉).toNat with hK
  have hpc : WassFSG.Lip.peelCount γ₁ τ t n = K + 1 := rfl
  -- `γ₁ ρ ≤ 2^K / n`, i.e. the lowest shell contributes at most `1/n`
  have hlow : ρ * (γ₁ / 2 ^ K) ≤ 1 / n := by
    have hx : 0 < γ₁ * Real.sqrt (τ * t * n) := by positivity
    have h1 : Real.logb 2 (γ₁ * Real.sqrt (τ * t * n)) ≤ (K : ℝ) := by
      have a1 := Int.le_ceil (Real.logb 2 (γ₁ * Real.sqrt (τ * t * n)))
      have a2 : (⌈Real.logb 2 (γ₁ * Real.sqrt (τ * t * n))⌉ : ℤ) ≤ (K : ℤ) := by
        rw [hK, Int.toNat_of_nonneg (le_max_left _ _)]; exact le_max_right _ _
      have a3 : ((⌈Real.logb 2 (γ₁ * Real.sqrt (τ * t * n))⌉ : ℤ) : ℝ) ≤ ((K : ℤ) : ℝ) := by
        exact_mod_cast a2
      push_cast at a3
      linarith
    have h2 : γ₁ * Real.sqrt (τ * t * n) ≤ 2 ^ K := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) hx] at h1
      simpa [Real.rpow_natCast] using h1
    have h3 : ρ * n = Real.sqrt (τ * t * n) := by
      have e : ρ * n = Real.sqrt (τ * t / n) * Real.sqrt ((n : ℝ) ^ 2) := by
        rw [Real.sqrt_sq hnR.le]
      rw [e, ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    have h4 : (0 : ℝ) < 2 ^ K := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ h4 hnR, one_mul]
    calc ρ * γ₁ * n = γ₁ * (ρ * n) := by ring
      _ ≤ 2 ^ K := by rw [h3]; exact h2
  -- the peeling classes
  let C : ℕ → Set (Z → ℝ) := fun k => if k = 0 then
      {f | f ∈ F ∧ WassFSG.Conc.lipNorm f ≤ γ₁ / 2 ^ K}
    else {f | f ∈ F ∧ γ₁ / 2 ^ k < WassFSG.Conc.lipNorm f ∧
      WassFSG.Conc.lipNorm f ≤ γ₁ / 2 ^ (k - 1)}
  have hCF : ∀ k, C k ⊆ F := by
    intro k f hf
    by_cases hk : k = 0
    · simp only [C, hk, if_true] at hf; exact hf.1
    · simp only [C, hk, if_false] at hf; exact hf.1
  have hCLip : ∀ k, WassFSG.Lip.LipBound γ₁ (C k) := fun k => ⟨hγ, fun f hf => hF.2 f (hCF k hf)⟩
  -- every `f ∈ F` lies in some class, where the sup of the Lipschitz norms is controlled
  have hcover : ∀ f ∈ F, ∃ k ∈ Finset.range (K + 1), f ∈ C k ∧
      ρ * (⨆ g : C k, WassFSG.Conc.lipNorm (g : Z → ℝ)) ≤
        2 * ρ * WassFSG.Conc.lipNorm f + 1 / n := by
    intro f hf
    have hL0 := lipNorm_nonneg f
    have hn1 : (0 : ℝ) ≤ 1 / n := by positivity
    have hbound : ∀ k, ∀ c, (∀ g ∈ C k, WassFSG.Conc.lipNorm g ≤ c) → f ∈ C k →
        (⨆ g : C k, WassFSG.Conc.lipNorm (g : Z → ℝ)) ≤ c := by
      intro k c hc hfk
      have : Nonempty (C k) := ⟨⟨f, hfk⟩⟩
      exact ciSup_le (fun g => hc g.1 g.2)
    by_cases hlo : WassFSG.Conc.lipNorm f ≤ γ₁ / 2 ^ K
    · refine ⟨0, by simp, ?_, ?_⟩
      · simp only [C, if_true]; exact ⟨hf, hlo⟩
      · have hfk : f ∈ C 0 := by simp only [C, if_true]; exact ⟨hf, hlo⟩
        have hs := hbound 0 (γ₁ / 2 ^ K) (fun g hg => by
          simp only [C, if_true] at hg; exact hg.2) hfk
        have := mul_le_mul_of_nonneg_left hs hρ0
        have : 0 ≤ 2 * ρ * WassFSG.Conc.lipNorm f := by positivity
        linarith
    · push Not at hlo
      have hex : ∃ j, γ₁ / 2 ^ j < WassFSG.Conc.lipNorm f := ⟨K, hlo⟩
      set j := Nat.find hex with hj
      have hjP : γ₁ / 2 ^ j < WassFSG.Conc.lipNorm f := Nat.find_spec hex
      have hjK : j ≤ K := Nat.find_min' hex hlo
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0, pow_zero, div_one] at hjP
        have := lipNorm_le f γ₁ hγ (hF.2 f hf)
        linarith
      have hjm : WassFSG.Conc.lipNorm f ≤ γ₁ / 2 ^ (j - 1) := by
        have := Nat.find_min hex (show j - 1 < j by omega)
        push Not at this
        exact this
      have hfk : f ∈ C j := by simp only [C, hj0, if_false]; exact ⟨hf, hjP, hjm⟩
      refine ⟨j, Finset.mem_range.2 (by omega), hfk, ?_⟩
      have hs := hbound j (γ₁ / 2 ^ (j - 1)) (fun g hg => by
        simp only [C, hj0, if_false] at hg; exact hg.2.2) hfk
      have h2 : γ₁ / 2 ^ (j - 1) = 2 * (γ₁ / 2 ^ j) := by
        have hpow : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [hpow]
        field_simp
      have h3 : ρ * (⨆ g : C j, WassFSG.Conc.lipNorm (g : Z → ℝ)) ≤
          2 * ρ * WassFSG.Conc.lipNorm f := by
        calc ρ * (⨆ g : C j, WassFSG.Conc.lipNorm (g : Z → ℝ)) ≤ ρ * (γ₁ / 2 ^ (j - 1)) :=
              mul_le_mul_of_nonneg_left hs hρ0
          _ = 2 * ρ * (γ₁ / 2 ^ j) := by rw [h2]; ring
          _ ≤ 2 * ρ * WassFSG.Conc.lipNorm f :=
              mul_le_mul_of_nonneg_left hjP.le (by positivity)
      linarith
  -- union bound over the `K + 1` classes, each handled by Lemma 11
  let B : ℕ → Set (Fin n → Z) := fun k => {z | ∃ f ∈ C k, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          (WassFSG.Lip.empMean z f : EReal)
            + ((Real.sqrt (τ * t / n) * ⨆ g : C k, WassFSG.Conc.lipNorm (g : Z → ℝ) : ℝ) : EReal)
            + 2 * WassFSG.Lip.expectedRad Ptrue n (C k))}
  have hsub : {z | ∃ f ∈ F, ¬ (((∫ x, f x ∂Ptrue : ℝ) : EReal) ≤
          ((WassFSG.Lip.empMean z f + 2 * Real.sqrt (τ * t / n) * WassFSG.Conc.lipNorm f : ℝ) :
            EReal)
            + 2 * WassFSG.Lip.expectedRad Ptrue n F + ((1 / (n : ℝ) : ℝ) : EReal))} ⊆
      ⋃ k ∈ Finset.range (K + 1), B k := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    obtain ⟨f, hf, hbad⟩ := hz
    obtain ⟨k, hk, hfk, hsup⟩ := hcover f hf
    refine Set.mem_biUnion hk ?_
    refine ⟨f, hfk, fun hgood => hbad (le_trans hgood ?_)⟩
    have hR := expectedRad_mono Ptrue n (C k) F (hCF k)
    have h1 : (WassFSG.Lip.empMean z f : EReal)
        + ((ρ * ⨆ g : C k, WassFSG.Conc.lipNorm (g : Z → ℝ) : ℝ) : EReal) ≤
        ((WassFSG.Lip.empMean z f + 2 * ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal)
          + ((1 / (n : ℝ) : ℝ) : EReal) := by
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
    have h2 : (2 : EReal) * WassFSG.Lip.expectedRad Ptrue n (C k) ≤
        2 * WassFSG.Lip.expectedRad Ptrue n F :=
      mul_le_mul_of_nonneg_left hR (by norm_num)
    calc (WassFSG.Lip.empMean z f : EReal)
          + ((ρ * ⨆ g : C k, WassFSG.Conc.lipNorm (g : Z → ℝ) : ℝ) : EReal)
          + 2 * WassFSG.Lip.expectedRad Ptrue n (C k)
        ≤ (((WassFSG.Lip.empMean z f + 2 * ρ * WassFSG.Conc.lipNorm f : ℝ) : EReal)
          + ((1 / (n : ℝ) : ℝ) : EReal)) + 2 * WassFSG.Lip.expectedRad Ptrue n F :=
          add_le_add h1 h2
      _ = _ := by rw [add_right_comm]
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _) ?_)
  have hk : ∀ k ∈ Finset.range (K + 1), (Measure.pi fun _ : Fin n => Ptrue) (B k) ≤
      ENNReal.ofReal (Real.exp (-t)) := fun k _ =>
    WassFSG.Lip.lemma_11 Ptrue τ hT (C k) γ₁ (hCLip k) t ht n hn
  refine le_trans (Finset.sum_le_sum hk) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hpc,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
