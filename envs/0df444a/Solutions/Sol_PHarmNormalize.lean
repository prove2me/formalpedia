-- Prove2me | solution 1 for PHarmNormalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:16:15.611319+00:00
-- url     : https://prove2.me/submissions/dff20eac-af82-432d-bb84-85028b34723b

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_NormalizedWeakGradient
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_PHigherOrder_PHarmNormalize
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_NormalizedWeakGradient
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport


set_option autoImplicit false
set_option linter.unusedVariables false
theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane) (x₀ : Plane) (r M c : ℝ)
    (hr : 0 < r) (hM : 0 < M) (h : IsPHarm p Ω u g) :
    IsPHarm p {x : Plane | x₀ + r • x ∈ Ω}
      (fun x => (u (x₀ + r • x) - c) / M)
      (fun x => (r / M) • g (x₀ + r • x)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hMne : M ≠ 0 := ne_of_gt hM
  have hrM : (0 : ℝ) < r / M := by positivity
  -- `T x = x₀ + r • x` and `S y = r⁻¹ • (y - x₀)` are mutually inverse affine homeomorphisms.
  have hST : ∀ x : Plane, r⁻¹ • ((x₀ + r • x) - x₀) = x := by
    intro x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrne, one_smul]
  have hTS : ∀ y : Plane, x₀ + r • (r⁻¹ • (y - x₀)) = y := by
    intro y
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
    abel
  have hTcont : Continuous (fun x : Plane => x₀ + r • x) := by fun_prop
  have hScont : Continuous (fun y : Plane => r⁻¹ • (y - x₀)) := by fun_prop
  have hTinj : Function.Injective (fun x : Plane => x₀ + r • x) := by
    intro a b hab
    have h1 : r • a = r • b := add_left_cancel hab
    exact smul_right_injective Plane hrne h1
  have hOopen : IsOpen Ω := h.openOmega
  have hOmeas : MeasurableSet Ω := hOopen.measurableSet
  -- (1) the rescaled domain is open, being a preimage under `T`.
  have hopen : IsOpen {x : Plane | x₀ + r • x ∈ Ω} := hOopen.preimage hTcont
  -- (2) continuity of the normalized function.
  have hcont : ContinuousOn (fun x : Plane => (u (x₀ + r • x) - c) / M)
      {x : Plane | x₀ + r • x ∈ Ω} := by
    have h1 : ContinuousOn (fun x : Plane => u (x₀ + r • x)) {x : Plane | x₀ + r • x ∈ Ω} :=
      h.contU.comp hTcont.continuousOn fun x hx => hx
    exact (h1.sub continuousOn_const).div_const M
  -- `T` is quasi measure preserving, so it pulls null sets back to null sets.
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : Plane => x₀ + r • x) MeasureTheory.volume MeasureTheory.volume := by
    have h1 : MeasureTheory.Measure.QuasiMeasurePreserving (fun x : Plane => r • x)
        MeasureTheory.volume MeasureTheory.volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume hrne]
      exact MeasureTheory.Measure.smul_absolutelyContinuous
    exact ((MeasureTheory.measurePreserving_add_left MeasureTheory.volume
      x₀).quasiMeasurePreserving).comp h1
  -- (3) a.e. strong measurability, through the strongly measurable representative of `g`.
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : Plane => (r / M) • g (x₀ + r • x))
      (MeasureTheory.volume.restrict {x : Plane | x₀ + r • x ∈ Ω}) := by
    have hmk : MeasureTheory.StronglyMeasurable (h.measG.mk g) := h.measG.stronglyMeasurable_mk
    have hcompmk : MeasureTheory.StronglyMeasurable
        (fun x : Plane => h.measG.mk g (x₀ + r • x)) := hmk.comp_measurable (by fun_prop)
    have hNnull : MeasureTheory.volume
        ({y : Plane | ¬ (g y = h.measG.mk g y)} ∩ Ω) = 0 := by
      have h0 : (MeasureTheory.volume.restrict Ω) {y : Plane | ¬ (g y = h.measG.mk g y)} = 0 :=
        MeasureTheory.ae_iff.mp h.measG.ae_eq_mk
      rwa [MeasureTheory.Measure.restrict_apply' hOmeas] at h0
    have hae : (fun x : Plane => h.measG.mk g (x₀ + r • x))
        =ᵐ[MeasureTheory.volume.restrict {x : Plane | x₀ + r • x ∈ Ω}]
          (fun x : Plane => g (x₀ + r • x)) := by
      refine MeasureTheory.ae_iff.mpr ?_
      have hsub : {x : Plane | ¬ (h.measG.mk g (x₀ + r • x) = g (x₀ + r • x))}
          ∩ {x : Plane | x₀ + r • x ∈ Ω}
          = (fun x : Plane => x₀ + r • x) ⁻¹' ({y : Plane | ¬ (g y = h.measG.mk g y)} ∩ Ω) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
        exact and_congr_left fun _ => by tauto
      rw [MeasureTheory.Measure.restrict_apply' hopen.measurableSet, hsub]
      exact hqmp.preimage_null hNnull
    exact (hcompmk.aestronglyMeasurable.congr hae).const_smul (r / M)
  -- (4) local integrability of `|G|^p`, through the indicator and the affine map.
  have hloc : ∀ K : Set Plane, K ⊆ {x : Plane | x₀ + r • x ∈ Ω} → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖(r / M) • g (x₀ + r • x)‖ ^ p) K := by
    intro K hK hKc
    have hKmeas : MeasurableSet K := hKc.measurableSet
    have hTKc : IsCompact ((fun x : Plane => x₀ + r • x) '' K) := hKc.image hTcont
    have hTKsub : (fun x : Plane => x₀ + r • x) '' K ⊆ Ω := by
      rintro y ⟨x, hx, rfl⟩
      exact hK hx
    have hbase : MeasureTheory.IntegrableOn (fun y => ‖g y‖ ^ p)
        ((fun x : Plane => x₀ + r • x) '' K) := h.locIntG _ hTKsub hTKc
    have hind : K.indicator (fun x => ‖g (x₀ + r • x)‖ ^ p)
        = fun x : Plane =>
            (((fun x : Plane => x₀ + r • x) '' K).indicator fun y => ‖g y‖ ^ p) (x₀ + r • x) := by
      funext x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        rintro ⟨x', hx', he⟩
        exact hx (hTinj he ▸ hx')
    have hcore : MeasureTheory.IntegrableOn (fun x => ‖g (x₀ + r • x)‖ ^ p) K := by
      rw [← MeasureTheory.integrable_indicator_iff hKmeas, hind]
      have hHint : MeasureTheory.Integrable
          (((fun x : Plane => x₀ + r • x) '' K).indicator fun y => ‖g y‖ ^ p) :=
        (MeasureTheory.integrable_indicator_iff hTKc.measurableSet).mpr hbase
      have h1 : MeasureTheory.Integrable (fun y : Plane =>
          (((fun x : Plane => x₀ + r • x) '' K).indicator fun y => ‖g y‖ ^ p) (x₀ + y)) :=
        ((MeasureTheory.measurePreserving_add_left MeasureTheory.volume x₀).integrable_comp_emb
          (MeasurableEquiv.addLeft x₀).measurableEmbedding).mpr hHint
      exact h1.comp_smul hrne
    have hpt : ∀ x : Plane, ‖(r / M) • g (x₀ + r • x)‖ ^ p
        = (r / M) ^ p * ‖g (x₀ + r • x)‖ ^ p := by
      intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrM, Real.mul_rpow hrM.le (norm_nonneg _)]
    simp only [hpt]
    exact hcore.const_mul _
  -- Vanishing off the topological support, and the whole-space affine change of variables.
  obtain ⟨hval0, hgrad0⟩ := VanishingOffTsupport
  have hcovP : ∀ F : Plane → Plane, ∫ x : Plane, F (x₀ + r • x)
      = |((r ^ (Module.finrank ℝ Plane))⁻¹)| • ∫ y : Plane, F y := by
    intro F
    rw [MeasureTheory.Measure.integral_comp_smul MeasureTheory.volume
      (fun y => F (x₀ + y)) r, MeasureTheory.integral_add_left_eq_self F x₀]
  have hcovR : ∀ F : Plane → ℝ, ∫ x : Plane, F (x₀ + r • x)
      = |((r ^ (Module.finrank ℝ Plane))⁻¹)| • ∫ y : Plane, F y := by
    intro F
    rw [MeasureTheory.Measure.integral_comp_smul MeasureTheory.volume
      (fun y => F (x₀ + y)) r, MeasureTheory.integral_add_left_eq_self F x₀]
  -- The test-function correspondence under the affine substitution, and the chain rule.
  have hpsi := AffineTestFunctionPullback x₀ r hr Ω
  refine ⟨hopen, hcont, hmeas, hloc, ?_, ?_⟩
  · -- (5) the distributional gradient identity.
    exact NormalizedWeakGradient p Ω u g x₀ r M c hr h
  · -- (6) the weak equation.
    intro φ hφ hφc hφsub
    obtain ⟨hψC, hψcs, hψsub, hψgrad⟩ := hpsi φ hφ hφc hφsub
    set ψ : Plane → ℝ := fun y : Plane => φ (r⁻¹ • (y - x₀)) with hψdef
    have hflux : ∀ ξ : Plane, PFlux p ((r / M) • ξ) = ((r / M) ^ (p - 1)) • PFlux p ξ := by
      intro ξ
      simp only [PFlux, norm_smul, Real.norm_eq_abs, abs_of_pos hrM]
      rw [Real.mul_rpow hrM.le (norm_nonneg _), smul_smul, smul_smul]
      congr 1
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hrM, Real.rpow_one]
      ring
    have hJ2 : ∫ y : Plane, inner ℝ (PFlux p (g y)) (gradient ψ y)
        = ∫ y in Ω, inner ℝ (PFlux p (g y)) (gradient ψ y) := by
      refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      rw [hgrad0 ψ y fun hcc => hy (hψsub hcc), inner_zero_right]
    have hJzero : ∫ y : Plane, inner ℝ (PFlux p (g y)) (gradient ψ y) = (0 : ℝ) := by
      rw [hJ2]
      exact h.eqn ψ hψC hψcs hψsub
    have hFint : ∀ x : Plane,
        (inner ℝ (PFlux p ((r / M) • g (x₀ + r • x))) (gradient φ x) : ℝ)
          = ((r / M) ^ (p - 1) * r)
              * inner ℝ (PFlux p (g (x₀ + r • x))) (gradient ψ (x₀ + r • x)) := by
      intro x
      rw [hflux (g (x₀ + r • x)), hψgrad x, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · calc ∫ x : Plane, (inner ℝ (PFlux p ((r / M) • g (x₀ + r • x))) (gradient φ x) : ℝ)
          = ∫ x : Plane, ((r / M) ^ (p - 1) * r)
              * inner ℝ (PFlux p (g (x₀ + r • x))) (gradient ψ (x₀ + r • x)) := by
              simp only [hFint]
        _ = ((r / M) ^ (p - 1) * r) * ∫ x : Plane,
              (inner ℝ (PFlux p (g (x₀ + r • x))) (gradient ψ (x₀ + r • x)) : ℝ) :=
              MeasureTheory.integral_const_mul _ _
        _ = ((r / M) ^ (p - 1) * r) * (|((r ^ (Module.finrank ℝ Plane))⁻¹)|
              • ∫ y : Plane, (inner ℝ (PFlux p (g y)) (gradient ψ y) : ℝ)) := by
              rw [hcovR (fun y => (inner ℝ (PFlux p (g y)) (gradient ψ y) : ℝ))]
        _ = (0 : ℝ) := by rw [hJzero]; simp
    · intro x hx
      rw [hgrad0 φ x fun hcc => hx (hφsub hcc), inner_zero_right]
