-- Prove2me | solution 1 for PI.VolStabW.induced_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:43.080517+00:00
-- url     : https://prove2.me/submissions/5d74e3d4-eb3a-4413-a1d2-459694100b8c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
import Theorems.Thm_PI_VolStabW_avg_out
import Theorems.Thm_PI_VolStabW_meas_avg_q
import Theorems.Thm_PI_VolStabW_meas_smul_q

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution (H : Subgroup G) (hcl : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] (ρ' : Measure (G ⧸ H))
    (hinv : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s)
    (hfin : ∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) (hne : ρ' ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' := by
  classical
  have : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite ν := inferInstance
  have hmulc : ∀ x : G, Measurable (fun h : H => x * (h : G)) := fun x =>
    (continuous_const.mul continuous_subtype_val).measurable
  set κ : G ⧸ H → Measure G := fun q => ν.map (fun h : H => q.out * (h : G)) with hκdef
  have hκA : ∀ (q : G ⧸ H) (A : Set G), MeasurableSet A →
      κ q A = ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν := by
    intro q A hA
    rw [← lintegral_indicator_one hA, hκdef]
    exact lintegral_map (measurable_one.indicator hA) (hmulc _)
  have hκ : Measurable κ := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have e : (fun q => κ q A) = fun q : G ⧸ H => ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν :=
      funext fun q => hκA q A hA
    rw [e]
    exact meas_avg_q H ν (measurable_one.indicator hA)
  set m : Measure G := ρ'.bind κ with hmdef
  have hmf : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂m = ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' := by
    intro f hf
    rw [hmdef, Measure.lintegral_bind hκ.aemeasurable hf.aemeasurable]
    apply lintegral_congr
    intro q
    exact lintegral_map hf (hmulc _)
  have hρmap : ∀ g : G, ρ'.map (fun q => g • q) = ρ' := by
    intro g
    ext s hs
    rw [Measure.map_apply (meas_smul_q H g) hs]
    exact hinv g s hs
  have hmA : ∀ A : Set G, MeasurableSet A →
      m A = ∫⁻ q, ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν ∂ρ' := by
    intro A hA
    rw [← lintegral_indicator_one hA]
    exact hmf _ (measurable_one.indicator hA)
  have hleft : m.IsMulLeftInvariant := by
    constructor
    intro g
    ext A hA
    rw [Measure.map_apply (measurable_const_mul g) hA, hmA _ (hA.preimage (measurable_const_mul g)),
      hmA A hA]
    have e : ∀ q : G ⧸ H, ∫⁻ h, ((fun x => g * x) ⁻¹' A).indicator 1 (q.out * (h : G)) ∂ν =
        (fun q' : G ⧸ H => ∫⁻ h, A.indicator 1 (q'.out * (h : G)) ∂ν) (g • q) := by
      intro q
      have h1 : g • q = ((g * q.out : G) : G ⧸ H) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      simp only
      rw [h1, avg_out H ν]
      apply lintegral_congr
      intro h
      simp only [Set.indicator, Set.mem_preimage, mul_assoc, Pi.one_apply]
    simp_rw [e]
    rw [← lintegral_map (meas_avg_q H ν (measurable_one.indicator hA)) (meas_smul_q H g), hρmap]

  have hfinm : IsFiniteMeasureOnCompacts m := by
    constructor
    intro K hK
    set S : Set H := (Subtype.val : H → G) ⁻¹' (K⁻¹ * K) with hSdef
    have hS : IsCompact S :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)
    have hbound : ∀ q : G ⧸ H, κ q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν S) q := by
      intro q
      rw [hκdef, Measure.map_apply (hmulc _) hK.isClosed.measurableSet]
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul H k
        rw [hh0]
        calc ν ((fun h : H => k * h0 * (h : G)) ⁻¹' K) ≤ ν ((fun h : H => h0 * h) ⁻¹' S) := by
              apply measure_mono
              intro h hh
              have hh' : k * (h0 : G) * (h : G) ∈ K := hh
              show ((h0 * h : H) : G) ∈ K⁻¹ * K
              rw [Subgroup.coe_mul]
              exact ⟨k⁻¹, Set.inv_mem_inv.2 hk, k * h0 * h, hh', by group⟩
          _ = ν S := measure_preimage_mul ν h0 S
      · rw [Set.indicator_of_notMem hq]
        apply le_of_eq
        apply measure_mono_null _ (measure_empty (μ := ν))
        intro h hh
        exfalso
        apply hq
        refine ⟨q.out * h, hh, ?_⟩
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rw [QuotientGroup.eq]
        simp
    rw [hmdef, Measure.bind_apply hK.isClosed.measurableSet hκ.aemeasurable]
    calc ∫⁻ q, κ q K ∂ρ' ≤ ∫⁻ q, ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
          (fun _ => ν S) q ∂ρ' := lintegral_mono hbound
      _ ≤ ν S * ρ' ((QuotientGroup.mk : G → G ⧸ H) '' K) := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top hS.measure_lt_top
          (hfin _ (hK.image QuotientGroup.continuous_mk))
  have hm : m = Measure.haarScalarFactor m μ • μ := Measure.isMulLeftInvariant_eq_smul m μ
  set c : ℝ≥0 := Measure.haarScalarFactor m μ with hcdef
  have hmne : m ≠ 0 := by
    intro h0
    have hu := hmA Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, lintegral_const, one_mul, lintegral_one] at hu
    rw [h0, Measure.coe_zero, Pi.zero_apply] at hu
    have hν : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν Set.univ_nonempty
    have hρ : ρ' Set.univ ≠ 0 := by
      intro h; exact hne (Measure.measure_univ_eq_zero.1 h)
    exact mul_ne_zero hν hρ hu.symm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    apply hmne
    rw [hm]
    ext s _
    simp [← hcdef, ENNReal.coe_eq_zero.1 h0]
  have hctop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.2 hctop, ENNReal.inv_ne_top.2 hc0, fun f hf => ?_⟩
  rw [← hmf f hf, hm]
  rw [show (c • μ : Measure G) = (c : ℝ≥0∞) • μ from rfl, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
end PI.VolStabW
