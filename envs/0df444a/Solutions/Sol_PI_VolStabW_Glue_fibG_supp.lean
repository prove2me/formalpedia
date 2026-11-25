-- Prove2me | solution 1 for PI.VolStabW.Glue.fibG_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:22.080806+00:00
-- url     : https://prove2.me/submissions/243dbcc7-f086-4231-9f70-c19a92ab3dbe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Theorems.Thm_PI_VolStabW_Glue_tsupport_extZ
import Theorems.Thm_PI_VolStabW_Glue_lam_apply
import Theorems.Thm_PI_VolStabW_DensGen_eq_zero_of_setIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.Glue
open MeasureTheory Topology Set Filter PI.VolStabW
open scoped CompactlySupported
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]
namespace PI.VolStabW.Glue
theorem _root_.solution (hD : DensAll μ f ι ν U) (hU : IsOpen U) (hf : Continuous f)
    (hι : Continuous ι) (b : X) : fibG hD hU b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hme : MeasurableEmbedding (Subtype.val : U → V) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  rw [fibG, hme.map_apply]
  have hOeq : (Subtype.val : U → V) ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ∘ Subtype.val) ⁻¹' {ι b}ᶜ := by
    ext u; simp [u.2]
  have hO : IsOpen ((f ∘ Subtype.val : U → Y) ⁻¹' {ι b}ᶜ) :=
    isOpen_compl_singleton.preimage (hf.comp continuous_subtype_val)
  rw [hOeq]
  refine le_antisymm ?_ bot_le
  rw [hO.measure_eq_iSup_isCompact]
  refine iSup_le fun K => iSup_le fun hKO => iSup_le fun hK => ?_
  obtain ⟨g, hg1, hgc, hgO, hg01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  let ψ : C_c(U, ℝ) := ⟨g, hgc⟩
  have hle := RealRMK.rieszMeasure_le_of_eq_one (lam hD hU b) (f := ψ) (fun x => (hg01 x).1) hK
    (fun x hx => hg1 hx)
  refine hle.trans (le_of_eq ?_)
  rw [lam_apply]
  have hcc : IsCcOn U (extZ U ψ) := extZ_props hU ψ ψ.continuous ψ.hasCompactSupport
  have hts := tsupport_extZ U ψ ψ.hasCompactSupport
  have hCc : IsCompact (f '' tsupport (extZ U ψ)) := hcc.2.1.image hf
  set N : Set X := (ι ⁻¹' (f '' tsupport (extZ U ψ)))ᶜ with hN
  have hNo : IsOpen N := (hCc.isClosed.preimage hι).isOpen_compl
  have hbN : b ∈ N := by
    rintro ⟨v, hv, hfv⟩
    obtain ⟨u, hu, rfl⟩ := hts hv
    exact hgO hu hfv
  have hz := DensGen.eq_zero_of_setIntegral (ν := ν) (G hD (extZ U ψ)) N b (hNo.mem_nhds hbN)
    (G_spec hD hcc).1.continuousOn (fun S hS hSN => by
      rw [← (G_spec hD hcc).2 S hS]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      by_contra hne
      obtain ⟨s, hs, hfs⟩ := hv
      exact hSN hs ⟨v, subset_tsupport _ hne, hfs.symm⟩)
  rw [hz, ENNReal.ofReal_zero]
end PI.VolStabW.Glue
