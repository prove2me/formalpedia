-- Prove2me | solution 1 for PI.VolStabSW.weil_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:29.161146+00:00
-- url     : https://prove2.me/submissions/8c0037d1-a097-4c85-8183-03c54fe1451a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Theorems.Thm_PI_VolStabSW_orb_mk
import Theorems.Thm_PI_VolStabSW_orb_smul
import Theorems.Thm_PI_weil_quotient_measure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
namespace PI.VolStabSW
theorem _root_.solution (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (hμr : μ.IsMulRightInvariant)
    (ν : Measure (MulAction.stabilizer G x0)) (hνH : ν.IsHaarMeasure) (hνr : ν.IsMulRightInvariant)
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX := by
  classical
  have := hνH
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  obtain ⟨ρ, hρ0, hρfin, hρinv, hρF, hρU⟩ :=
    PI.weil_quotient_measure G (MulAction.stabilizer G x0) hcl μ ν inferInstance hμr inferInstance hνr

  have hrange : ∀ y, y ∈ Set.range ι ↔ ∃ g : G, g • x0 = y := by
    intro y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.out, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ MulAction.stabilizer G x0), orb_mk x0 g⟩
  set ρ' : Measure (G ⧸ MulAction.stabilizer G x0) := νX.comap ι with hρ'def
  have hmap : ρ'.map ι = νX := by
    rw [hρ'def, hemb.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    convert hnull using 2
    ext y
    simp only [Set.mem_ofPred_eq, hrange]
  have hρ'inv : ∀ (g : G) (s : Set (G ⧸ MulAction.stabilizer G x0)), MeasurableSet s →
      ρ' ((fun y => g • y) ⁻¹' s) = ρ' s := by
    intro g s hs
    rw [hρ'def, hemb.comap_apply, hemb.comap_apply]
    have himg : ι '' ((fun y => g • y) ⁻¹' s) = (fun y => g • y) ⁻¹' (ι '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, orb_smul x0 g q⟩
      · rintro ⟨q', hq', hy⟩
        refine ⟨g⁻¹ • q', by simpa [smul_smul] using hq', ?_⟩
        show (g⁻¹ • q').out • x0 = y
        rw [orb_smul x0 g⁻¹ q']
        show g⁻¹ • ι q' = y
        rw [hy, inv_smul_smul]
    rw [himg]
    exact hinv g _ (hemb.measurableSet_image.2 hs)
  have hρ'fin : ∀ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K → ρ' K < ⊤ := by
    intro K hK
    rw [hρ'def, hemb.comap_apply]
    exact hfin _ (hK.image hcont)
  have hρ'ne : ρ' ≠ 0 := by
    intro h0
    apply hne
    rw [← hmap, h0, Measure.map_zero]
  obtain ⟨c, hc⟩ := hρU ρ' hρ'fin hρ'inv
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hρ'ne (by rw [hc, zero_smul])

  have hK : ∃ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K ∧ ρ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hρ0
    apply Measure.measure_univ_eq_zero.1
    apply measure_mono_null (t := ⋃ n, (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) '' compactCovering G n)
    · intro q _
      rw [Set.mem_iUnion]
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering G).symm ▸ Set.mem_univ q.out)
      exact ⟨n, q.out, hn, QuotientGroup.out_eq' q⟩
    · exact measure_iUnion_null fun n =>
        hcon _ ((isCompact_compactCovering G n).image QuotientGroup.continuous_mk)
  have hctop : c ≠ ⊤ := by
    rintro rfl
    obtain ⟨K, hKc, hKpos⟩ := hK
    have := hρ'fin K hKc
    rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hKpos] at this
    exact lt_irrefl _ this
  refine ⟨c⁻¹ • ν, Measure.IsHaarMeasure.smul ν (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0), ?_⟩
  intro f hf s hs
  rw [hρF f hf]
  have hin : ∀ q : G ⧸ MulAction.stabilizer G x0, ∫⁻ h', f (s (ι q) * (h' : G)) ∂(c⁻¹ • ν) =
      c⁻¹ * ∫⁻ h, f (q.out * (h : G)) ∂ν := by
    intro q
    rw [lintegral_smul_measure]
    congr 1
    have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
    have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
    have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
    rw [hsk]
    have := lintegral_mul_left_eq_self (μ := ν) (fun h : MulAction.stabilizer G x0 => f (q.out * (h : G)))
      ⟨q.out⁻¹ * s (ι q), hk⟩
    simpa [mul_assoc] using this
  rw [← hmap, hemb.lintegral_map, hc, lintegral_smul_measure]
  simp_rw [hin]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hctop, one_mul]
end PI.VolStabSW
