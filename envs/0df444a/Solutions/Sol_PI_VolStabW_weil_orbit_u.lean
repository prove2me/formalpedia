-- Prove2me | solution 1 for PI.VolStabW.weil_orbit_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:54.348429+00:00
-- url     : https://prove2.me/submissions/a7013493-3db7-4c88-8e05-778dbd430fa4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
import Theorems.Thm_PI_VolStabW_induced_eq
import Theorems.Thm_PI_VolStabW_orb_mk
import Theorems.Thm_PI_VolStabW_orb_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal NNReal Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX := by
  classical
  have : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
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
  set ν : Measure (MulAction.stabilizer G x0) := Measure.haar with hνdef
  obtain ⟨c, hc0, hctop, hF⟩ := induced_eq (MulAction.stabilizer G x0) hcl μ ν ρ' hρ'inv hρ'fin hρ'ne
  refine ⟨c • ν, Measure.IsHaarMeasure.smul ν hc0 hctop, ?_⟩
  intro f hf s hs
  rw [hF f hf]
  have hin : ∀ q : G ⧸ MulAction.stabilizer G x0, ∫⁻ h', f (s (ι q) * (h' : G)) ∂(c • ν) =
      c * ∫⁻ h, f (q.out * (h : G)) ∂ν := by
    intro q
    rw [lintegral_smul_measure, smul_eq_mul]
    congr 1
    have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
    have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
    have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
    rw [hsk]
    have := lintegral_mul_left_eq_self (μ := ν)
      (fun h : MulAction.stabilizer G x0 => f (q.out * (h : G))) ⟨q.out⁻¹ * s (ι q), hk⟩
    simpa [mul_assoc] using this
  rw [← hmap, hemb.lintegral_map]
  simp_rw [hin]
  rw [lintegral_const_mul' _ _ hctop]
end PI.VolStabW
