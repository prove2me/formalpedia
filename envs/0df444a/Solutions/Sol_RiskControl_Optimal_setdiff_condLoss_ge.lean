-- Prove2me | solution 1 for RiskControl.Optimal.setdiff_condLoss_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:57:53.204799+00:00
-- url     : https://prove2.me/submissions/278b90af-7a6b-42ba-8cc8-877a905487bc

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RiskControl.Optimal

lemma rco_lint {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (A : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1}) :
    ∫⁻ p, ∫⁻ z in A p.1, (ℓ p.2 z : ℝ≥0∞) ∂μ ∂P
      = ∫⁻ x, ∫⁻ z in A x, condLoss κ ℓ x z ∂μ ∂P.fst := by
  classical
  have hAx : ∀ x, MeasurableSet (A x) := fun x => measurable_prodMk_left hA
  -- the jointly measurable integrand
  let H : (𝒳 × 𝒴) × 𝒵 → ℝ≥0∞ := fun q => if q.2 ∈ A q.1.1 then (ℓ q.1.2 q.2 : ℝ≥0∞) else 0
  have hHmeas : Measurable H := by
    have hset : MeasurableSet {q : (𝒳 × 𝒴) × 𝒵 | q.2 ∈ A q.1.1} :=
      hA.preimage (f := fun q : (𝒳 × 𝒴) × 𝒵 => (q.1.1, q.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hl : Measurable (fun q : (𝒳 × 𝒴) × 𝒵 => (ℓ q.1.2 q.2 : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp (hℓ.comp (f := fun q : (𝒳 × 𝒴) × 𝒵 => (q.1.2, q.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact Measurable.ite hset hl measurable_const
  have hlhs : ∀ p : 𝒳 × 𝒴, ∫⁻ z in A p.1, (ℓ p.2 z : ℝ≥0∞) ∂μ = ∫⁻ z, H (p, z) ∂μ := by
    intro p
    rw [← lintegral_indicator (hAx p.1)]
    apply lintegral_congr
    intro z
    simp [H, Set.indicator]
  simp_rw [hlhs]
  have hfm : Measurable (fun p : 𝒳 × 𝒴 => ∫⁻ z, H (p, z) ∂μ) :=
    hHmeas.lintegral_prod_right'
  have e1 : ∫⁻ p, ∫⁻ z, H (p, z) ∂μ ∂P = ∫⁻ p, ∫⁻ z, H (p, z) ∂μ ∂(P.fst ⊗ₘ κ) := by rw [hκ]
  rw [e1, Measure.lintegral_compProd hfm]
  apply lintegral_congr
  intro x
  have hm2 : Measurable (fun q : 𝒴 × 𝒵 => H ((x, q.1), q.2)) :=
    hHmeas.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable, ← lintegral_indicator (hAx x)]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A x
  · simp [H, hz, Set.indicator, condLoss]
  · simp [H, hz, Set.indicator]


theorem solution {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (hR : risk P μ ℓ T' ≤ risk P μ ℓ (thresholdSet κ ℓ lam)) :
    ∫⁻ x, ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ ∂P.fst
      ≤ ∫⁻ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ∂P.fst := by
  classical
  set c0 : ℝ≥0∞ := ENNReal.ofReal (-lam) with hc0
  have hc0top : c0 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- joint measurability of the conditional loss
  have hmc : Measurable (fun q : 𝒳 × 𝒵 => condLoss κ ℓ q.1 q.2) := by
    have hf : Measurable (Function.uncurry (fun (q : 𝒳 × 𝒵) (y : 𝒴) => (ℓ y q.2 : ℝ≥0∞))) :=
      measurable_coe_nnreal_ennreal.comp
        (hℓ.comp (f := fun p : (𝒳 × 𝒵) × 𝒴 => (p.2, p.1.2))
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    have := Measurable.lintegral_kernel_prod_right
      (κ := Kernel.comap κ Prod.fst measurable_fst) hf
    simpa [condLoss, Kernel.comap_apply] using this
  set Tl : 𝒳 → Set 𝒵 := thresholdSet κ ℓ lam with hTl
  have hTlg : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ Tl q.1} :=
    measurableSet_le measurable_const hmc
  have hsec : ∀ (S : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      ∀ x, MeasurableSet (S x) := fun S hS x => measurable_prodMk_left hS
  have hcompl : ∀ (S : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ (S q.1)ᶜ} := fun S hS => hS.compl
  have hinter : ∀ (S R : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ R q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1 ∩ R q.1} := fun S R hS hR => hS.inter hR
  have hdiff : ∀ (S R : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ R q.1} →
      MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1 \ R q.1} := fun S R hS hR => hS.diff hR
  -- measurability of the x-integrals
  have hmJ : ∀ (S : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      Measurable (fun x => ∫⁻ z in S x, condLoss κ ℓ x z ∂μ) := by
    intro S hS
    have hG : Measurable (fun q : 𝒳 × 𝒵 => if q.2 ∈ S q.1 then condLoss κ ℓ q.1 q.2 else 0) :=
      Measurable.ite hS hmc measurable_const
    have := hG.lintegral_prod_right' (ν := μ)
    convert this using 2 with x
    rw [← lintegral_indicator (hsec S hS x)]
    apply lintegral_congr
    intro z
    simp [Set.indicator]
  -- risk as an iterated integral
  have hrisk : ∀ (S : 𝒳 → Set 𝒵), MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ S q.1} →
      risk P μ ℓ S = ∫⁻ x, ∫⁻ z in (S x)ᶜ, condLoss κ ℓ x z ∂μ ∂P.fst := by
    intro S hS
    unfold risk setLoss
    exact rco_lint P μ ℓ hℓ κ hκ (fun x => (S x)ᶜ) (hcompl S hS)
  rw [hrisk T' hT', hrisk Tl hTlg] at hR
  have hTx := hsec T' hT'
  have hTlx := hsec Tl hTlg
  -- pointwise decompositions
  have hd1 : ∀ x, ∫⁻ z in (T' x)ᶜ, condLoss κ ℓ x z ∂μ =
      ∫⁻ z in (T' x)ᶜ ∩ (Tl x)ᶜ, condLoss κ ℓ x z ∂μ
        + ∫⁻ z in Tl x \ T' x, condLoss κ ℓ x z ∂μ := by
    intro x
    have h := lintegral_inter_add_diff (μ := μ) (fun z => condLoss κ ℓ x z) (T' x)ᶜ (hTlx x).compl
    have hs : (T' x)ᶜ \ (Tl x)ᶜ = Tl x \ T' x := by ext z; simp; tauto
    rw [hs] at h
    exact h.symm
  have hd2 : ∀ x, ∫⁻ z in (Tl x)ᶜ, condLoss κ ℓ x z ∂μ =
      ∫⁻ z in (T' x)ᶜ ∩ (Tl x)ᶜ, condLoss κ ℓ x z ∂μ
        + ∫⁻ z in T' x \ Tl x, condLoss κ ℓ x z ∂μ := by
    intro x
    have h := lintegral_inter_add_diff (μ := μ) (fun z => condLoss κ ℓ x z) (Tl x)ᶜ (hTx x).compl
    have hs : (Tl x)ᶜ \ (T' x)ᶜ = T' x \ Tl x := by ext z; simp; tauto
    have hs2 : (Tl x)ᶜ ∩ (T' x)ᶜ = (T' x)ᶜ ∩ (Tl x)ᶜ := Set.inter_comm _ _
    rw [hs, hs2] at h
    exact h.symm
  have hgB : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ (T' q.1)ᶜ ∩ (Tl q.1)ᶜ} :=
    hinter (fun x => (T' x)ᶜ) (fun x => (Tl x)ᶜ) (hcompl T' hT') (hcompl Tl hTlg)
  have hmB := hmJ (fun x => (T' x)ᶜ ∩ (Tl x)ᶜ) hgB
  simp_rw [hd1, hd2] at hR
  rw [lintegral_add_left hmB, lintegral_add_left hmB] at hR
  -- finiteness
  have hfin : ∫⁻ x, ∫⁻ z in (Tl x)ᶜ, condLoss κ ℓ x z ∂μ ∂P.fst ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∫⁻ x, c0 * μ Set.univ ∂P.fst)
    · rw [lintegral_const, measure_univ (μ := P.fst), mul_one]
      exact ENNReal.mul_ne_top hc0top (measure_ne_top _ _)
    · apply lintegral_mono
      intro x
      calc ∫⁻ z in (Tl x)ᶜ, condLoss κ ℓ x z ∂μ ≤ ∫⁻ z in (Tl x)ᶜ, c0 ∂μ := by
            apply setLIntegral_mono' (hTlx x).compl
            intro z hz
            have : ¬ (c0 ≤ condLoss κ ℓ x z) := hz
            exact (not_le.mp this).le
        _ = c0 * μ (Tl x)ᶜ := by rw [setLIntegral_const, mul_comm]
        _ ≤ c0 * μ Set.univ := mul_le_mul le_rfl (measure_mono (Set.subset_univ _)) zero_le zero_le
  have hfinB : ∫⁻ x, ∫⁻ z in (T' x)ᶜ ∩ (Tl x)ᶜ, condLoss κ ℓ x z ∂μ ∂P.fst ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    apply lintegral_mono
    intro x
    exact lintegral_mono_set (Set.inter_subset_right)
  exact (ENNReal.add_le_add_iff_left hfinB).mp hR
