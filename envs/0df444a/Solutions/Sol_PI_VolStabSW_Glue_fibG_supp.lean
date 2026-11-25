-- Prove2me | solution 1 for PI.VolStabSW.Glue.fibG_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:49.765567+00:00
-- url     : https://prove2.me/submissions/c2152327-0d4e-4beb-8ffb-4153c389eeb8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Theorems.Thm_PI_VolStabSW_Glue_tsupport_extZ
import Theorems.Thm_PI_VolStabSW_Glue_lam_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW.Glue
open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported
section Ext
variable {V : Type} [TopologicalSpace V] [T2Space V]
end Ext
section Dens
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
variable [OpensMeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
variable [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace V]
end Dens
section Riesz
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]
private theorem nonpos_of_setIntegral_compact_nonpos {g : X → ℝ} (hg : Continuous g) {b : X} {N : Set X} (hN : N ∈ 𝓝 b)
    (h : ∀ S, IsCompact S → S ⊆ N → ∫ x in S, g x ∂ν ≤ 0) : g b ≤ 0 := by
  refine not_lt.mp fun hpos => ?_
  have hW : N ∩ {x | g b / 2 < g x} ∈ 𝓝 b :=
    inter_mem hN ((isOpen_lt continuous_const hg).mem_nhds (show g b / 2 < g b by linarith))
  obtain ⟨K, hKn, hKW, hK⟩ := local_compact_nhds hW
  have hlow : ∫ x in K, g b / 2 ∂ν ≤ ∫ x in K, g x ∂ν :=
    setIntegral_mono_on (continuous_const.continuousOn.integrableOn_compact hK)
      (hg.continuousOn.integrableOn_compact hK) hK.isClosed.measurableSet
      (fun x hx => (hKW hx).2.le)
  have hconst : 0 < ∫ x in K, g b / 2 ∂ν := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_pos (ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hKn).ne' hK.measure_lt_top.ne)
      (half_pos hpos)
  linarith [h K hK (fun x hx => (hKW hx).1)]
end Riesz
end PI.VolStabSW.Glue
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.Glue
open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]
namespace PI.VolStabSW.Glue
theorem _root_.solution (hD : DensAll μ f ι ν U) (hU : IsOpen U) (hf : Continuous f)
    (hι : Continuous ι) (b : X) : fibG hD hU b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hW : IsOpen {u : U | f u ≠ ι b} :=
    isOpen_ne_fun (hf.comp continuous_subtype_val) continuous_const
  have hpre : (Subtype.val : U → V) ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = {u : U | f u ≠ ι b} := by
    ext u
    simp
  have hmeas : MeasurableSet (f ⁻¹' {ι b} ∩ U)ᶜ :=
    ((isClosed_singleton.preimage hf).measurableSet.inter hU.measurableSet).compl
  have hzero : ∀ K : Set U, K ⊆ {u : U | f u ≠ ι b} → IsCompact K →
      RealRMK.rieszMeasure (lam hD hU b) K = 0 := by
    intro K hKW hK
    obtain ⟨g, hg1, hgc, hgW, hg01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hW hKW
    let ψ : C_c(U, ℝ) := ⟨g, hgc⟩
    have hcc := extZ_props hU ψ ψ.continuous ψ.hasCompactSupport
    obtain ⟨hGc, hGi⟩ := G_spec hD hcc
    have hK' : IsCompact (Subtype.val '' tsupport ψ) :=
      ψ.hasCompactSupport.isCompact.image continuous_subtype_val
    have hbK : ι b ∉ f '' (Subtype.val '' tsupport ψ) := by
      rintro ⟨v, ⟨u, hu, rfl⟩, hv⟩
      exact hgW hu hv
    have hN : ι ⁻¹' (f '' (Subtype.val '' tsupport ψ))ᶜ ∈ 𝓝 b :=
      ((hK'.image hf).isClosed.isOpen_compl.preimage hι).mem_nhds hbK
    have hSz : ∀ S, IsCompact S → S ⊆ ι ⁻¹' (f '' (Subtype.val '' tsupport ψ))ᶜ →
        ∫ x in S, G hD (extZ U ψ) x ∂ν = 0 := by
      intro S hS hSN
      rw [← hGi S hS]
      apply setIntegral_eq_zero_of_forall_eq_zero
      rintro v ⟨s, hs, hsv⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hvt
      exact hSN hs ⟨v, tsupport_extZ U ψ ψ.hasCompactSupport hvt, hsv.symm⟩
    have hup := nonpos_of_setIntegral_compact_nonpos (ν := ν) hGc hN fun S hS hSN => (hSz S hS hSN).le
    have hdown := nonpos_of_setIntegral_compact_nonpos (ν := ν) hGc.neg hN fun S hS hSN => by
      simp only [Pi.neg_apply]
      rw [integral_neg, hSz S hS hSN, neg_zero]
    have hΛ : lam hD hU b ψ = 0 := by
      rw [lam_apply]
      exact le_antisymm hup (neg_nonpos.mp hdown)
    have hle := RealRMK.rieszMeasure_le_of_eq_one (lam hD hU b) (f := ψ) (fun x => (hg01 x).1) hK
      (fun x hx => hg1 hx)
    rw [hΛ, ENNReal.ofReal_zero] at hle
    exact le_antisymm hle bot_le
  unfold fibG
  rw [Measure.map_apply continuous_subtype_val.measurable hmeas, hpre,
    hW.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  exact hzero
end PI.VolStabSW.Glue
