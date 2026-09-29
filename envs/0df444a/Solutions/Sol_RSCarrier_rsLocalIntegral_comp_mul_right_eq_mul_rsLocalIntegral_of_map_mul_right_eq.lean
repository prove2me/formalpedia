-- Prove2me | solution 1 for RSCarrier.rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b34ef115-ff6f-5840-be6e-f9bad6825941

import Mathlib
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_RSCarrier
import Theorems.Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace RSCarrierMulRight

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem measurable_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.mul measurable_const).mul
        (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

theorem measurable_density [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

end Density

section Transfer

variable {G : Type*} [Group G]

@[reducible] def invariantSigma (m : MeasurableSpace G) (H : Subgroup G) : MeasurableSpace G where
  MeasurableSet' s := MeasurableSet[m] s ∧ ∀ x ∈ H, (fun g => x * g) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun x hx => by rw [Set.preimage_compl, hs.2 x hx]⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun x hx => by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hf i).2 x hx⟩

theorem invariantSigma_le (m : MeasurableSpace G) (H : Subgroup G) : invariantSigma m H ≤ m :=
  fun _ hs => hs.1

theorem measurable_invariantSigma {m : MeasurableSpace G} {H : Subgroup G} {β : Type*} [MeasurableSpace β]
    {Φ : G → β} (hΦ : Measurable[m] Φ) (hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g) :
    Measurable[invariantSigma m H] Φ := by
  intro t ht
  refine ⟨hΦ ht, fun x hx => ?_⟩
  ext g
  simp only [Set.mem_preimage, hΦH x hx g]

theorem trim_eq_trim_of_forall_lintegral_eq {m : MeasurableSpace G} (H : Subgroup G) (μ ν : Measure G)
    (hμν : ∀ f : G → ℝ≥0∞, Measurable f → (∀ x ∈ H, ∀ g : G, f (x * g) = f g) → ∫⁻ g, f g ∂μ = ∫⁻ g, f g ∂ν) :
    μ.trim (invariantSigma_le m H) = ν.trim (invariantSigma_le m H) := by
  refine @Measure.ext _ (invariantSigma m H) _ _ fun s hs => ?_
  rw [trim_measurableSet_eq _ hs, trim_measurableSet_eq _ hs]
  obtain ⟨hsm, hsH⟩ := hs
  have hind : ∀ x ∈ H, ∀ g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (x * g) = s.indicator (fun _ => (1 : ℝ≥0∞)) g := by
    intro x hx g
    have hmem : x * g ∈ s ↔ g ∈ s := by
      constructor
      · intro h
        have : g ∈ (fun g => x * g) ⁻¹' s := h
        rwa [hsH x hx] at this
      · intro h
        have : g ∈ (fun g => x * g) ⁻¹' s := by rwa [hsH x hx]
        exact this
    by_cases hg : g ∈ s
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.mp h))]
  have := hμν (s.indicator fun _ => 1) (measurable_const.indicator hsm) hind
  rwa [lintegral_indicator_const hsm, lintegral_indicator_const hsm, one_mul, one_mul] at this

theorem integral_eq_of_forall_lintegral_eq {m : MeasurableSpace G} (H : Subgroup G) (μ ν : Measure G)
    (hμν : ∀ f : G → ℝ≥0∞, Measurable f → (∀ x ∈ H, ∀ g : G, f (x * g) = f g) → ∫⁻ g, f g ∂μ = ∫⁻ g, f g ∂ν)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Φ : G → E) (hΦ : Measurable Φ) (hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g) :
    ∫ g, Φ g ∂μ = ∫ g, Φ g ∂ν := by
  have hle := invariantSigma_le m H
  have hsm : StronglyMeasurable[invariantSigma m H] Φ :=
    @Measurable.stronglyMeasurable _ _ _ (invariantSigma m H) _ _ _ _ _ (measurable_invariantSigma hΦ hΦH)
  rw [integral_trim hle hsm, integral_trim hle hsm, trim_eq_trim_of_forall_lintegral_eq H μ ν hμν]

end Transfer

section Delta

variable {G : Type*} [Group G]

theorem delta_one {δ : G → ℝ} (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k) : δ 1 = 1 := by
  have h : δ 1 * δ 1 = δ 1 * 1 := by rw [mul_one, ← hδmul, mul_one]
  exact mul_left_cancel₀ (hδpos 1).ne' h

theorem delta_inv_mul {δ : G → ℝ} (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k) (h : G) :
    δ h⁻¹ * δ h = 1 := by
  rw [← hδmul, inv_mul_cancel, delta_one hδpos hδmul]

theorem cpow_inv_mul_cpow_mul {δ : G → ℝ} (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k)
    (g h : G) (r : ℂ) :
    ((δ h⁻¹ : ℝ) : ℂ) ^ r * ((δ (g * h) : ℝ) : ℂ) ^ r = ((δ g : ℝ) : ℂ) ^ r := by
  rw [← Complex.mul_cpow_ofReal_nonneg (hδpos _).le (hδpos _).le, ← Complex.ofReal_mul, hδmul, mul_comm (δ g) (δ h),
    ← mul_assoc, delta_inv_mul hδpos hδmul, one_mul]

theorem cpow_ne_zero_of_pos {a : ℝ} (ha : 0 < a) (r : ℂ) : ((a : ℝ) : ℂ) ^ r ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast ha.ne'))

end Delta

end RSCarrierMulRight

end

open MeasureTheory RSCarrierMulRight
open scoped NNReal ENNReal Pointwise

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (h : G) (hμh : Measure.map (· * h) μ = μ)
    (δ : G → ℝ) (hδ : Measurable δ) (hδpos : ∀ g : G, 0 < δ g) (hδmul : ∀ g k : G, δ (g * k) = δ g * δ k)
    (hδH : ∀ x ∈ H, ∀ g : G, δ (x * g) = δ g)
    (s : ℂ) (W F : G → ℂ) (hW : Measurable W) (hF : Measurable F)
    (hWF : ∀ x ∈ H, ∀ g k : G, W (x * g) * F (x * k) = W g * F k) :
    (Integrable (fun g : G => (W g * F (g * h)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity (HaarQuotient.density H
      μH)) ↔ Integrable (fun g : G => (W (g * h⁻¹) * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (μ.withDensity
      (HaarQuotient.density H μH))) ∧
      RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => F (g * h)) = ((δ h⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) *
        RSCarrier.rsLocalIntegral μ H μH δ s (fun g => W (g * h⁻¹)) F := by
  set D : G → ℝ≥0∞ := HaarQuotient.density H μH with hD
  set ν : Measure G := μ.withDensity D with hν
  have hDm : Measurable D := measurable_density H μH

  set Φ : G → ℂ := fun g => (W (g * h⁻¹) * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) with hΦ
  set Φ₁ : G → ℂ := fun g => (W g * F (g * h)) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) with hΦ₁
  set c : ℂ := ((δ h⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) with hc
  have hc0 : c ≠ 0 := cpow_ne_zero_of_pos (hδpos _) _
  have hδC : Measurable fun g : G => ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) :=
    (Complex.measurable_ofReal.comp hδ).pow_const _
  have hΦm : Measurable Φ := ((hW.comp (measurable_mul_const h⁻¹)).mul hF).mul hδC
  have hΦ₁m : Measurable Φ₁ := (hW.mul (hF.comp (measurable_mul_const h))).mul hδC
  have hΦhm : Measurable fun g => Φ (g * h) := hΦm.comp (measurable_mul_const h)
  have hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g := by
    intro x hx g
    simp only [hΦ, mul_assoc x g h⁻¹, hWF x hx (g * h⁻¹) g, hδH x hx g]

  have hΦ₁eq : ∀ g : G, Φ₁ g = c * Φ (g * h) := by
    intro g
    simp only [hΦ₁, hΦ, hc, mul_inv_cancel_right]
    rw [mul_left_comm, cpow_inv_mul_cpow_mul hδpos hδmul g h]
  have hΦ₁eq' : Φ₁ = fun g => c * Φ (g * h) := funext hΦ₁eq

  have hlin : ∀ f : G → ℝ≥0∞, Measurable f → (∀ x ∈ H, ∀ g : G, f (x * g) = f g) →
      ∫⁻ g, f (g * h) ∂ν = ∫⁻ g, f g ∂ν := by
    intro f hf hfH
    rw [hν, lintegral_withDensity_eq_lintegral_mul μ hDm (show Measurable (fun g : G => f (g * h)) from
        hf.comp (measurable_mul_const h)),
      lintegral_withDensity_eq_lintegral_mul μ hDm hf]
    simp only [Pi.mul_apply, hD]
    exact HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq μ H hH μH f hf hfH h hμh

  have hnorm : ∫⁻ g, ‖Φ (g * h)‖ₑ ∂ν = ∫⁻ g, ‖Φ g‖ₑ ∂ν :=
    hlin (fun g => ‖Φ g‖ₑ) hΦm.enorm fun x hx g => by simp only [hΦH x hx g]
  have hint : Integrable (fun g => Φ (g * h)) ν ↔ Integrable Φ ν := by
    constructor
    · intro hI
      refine ⟨hΦm.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, ← hnorm]
      exact hI.2
    · intro hI
      refine ⟨hΦhm.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, hnorm]
      exact hI.2
  have hint₁ : Integrable Φ₁ ν ↔ Integrable Φ ν := by
    rw [hΦ₁eq', integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc0)]
    exact hint
  refine ⟨hint₁, ?_⟩

  set e : G ≃ᵐ G := MeasurableEquiv.mulRight h with he
  have hex : ∀ g : G, e g = g * h := fun g => rfl
  have h1 : ∫ g, Φ (g * h) ∂ν = ∫ g, Φ g ∂(Measure.map e ν) := by
    rw [integral_map_equiv]
    simp only [hex]
  have hagree : ∀ f : G → ℝ≥0∞, Measurable f → (∀ y ∈ H, ∀ g : G, f (y * g) = f g) →
      ∫⁻ g, f g ∂(Measure.map e ν) = ∫⁻ g, f g ∂ν := by
    intro f hf hfH
    rw [lintegral_map_equiv]
    exact hlin f hf hfH
  have hval : ∫ g, Φ (g * h) ∂ν = ∫ g, Φ g ∂ν := by
    rw [h1, integral_eq_of_forall_lintegral_eq H _ _ hagree Φ hΦm hΦH]
  show ∫ g, Φ₁ g ∂ν = c * ∫ g, Φ g ∂ν
  rw [hΦ₁eq', integral_const_mul, hval]

end S_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq
end P2MW
export P2MW.S_RSCarrier_rsLocalIntegral_comp_mul_right_eq_mul_rsLocalIntegral_of_map_mul_right_eq (solution)
