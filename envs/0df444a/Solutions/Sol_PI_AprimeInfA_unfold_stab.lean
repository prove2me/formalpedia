-- Prove2me | solution 1 for PI.AprimeInfA.unfold_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:19.143473+00:00
-- url     : https://prove2.me/submissions/a02748cb-0456-4863-bb42-f11db2df5120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Theorems.Thm_PI_AprimeInfA_polish_of_lcsc
import Theorems.Thm_PI_AprimeInfA_lintegral_mul_right_of_mem
import Theorems.Thm_PI_AprimeInfA_avg_mul_mem
import Theorems.Thm_PI_AprimeInfA_avg_out
import Theorems.Thm_PI_AprimeInfA_meas_avg_q
import Theorems.Thm_PI_AprimeInfA_orb_mk
import Theorems.Thm_PI_AprimeInfA_orb_cont
import Theorems.Thm_PI_AprimeInfA_orb_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
namespace PI.AprimeInfA
theorem _root_.solution (x0 : X) (hc : Continuous fun g : G => g • x0) (μ : Measure G)
    [μ.IsHaarMeasure] (ν : Measure (MulAction.stabilizer G x0)) (hν : ν.IsMulLeftInvariant)
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (f : G → ℝ≥0∞) (hf : Measurable f) (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) :
    ∫⁻ g, f g ∂μ = (ν univ)⁻¹ *
      ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂ν ∂(μ.map (fun g => g • x0)) := by
  haveI := hν
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  have hS : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := by
    have e : ((MulAction.stabilizer G x0 : Subgroup G) : Set G) = (fun g : G => g • x0) ⁻¹' {x0} := by
      ext g
      exact MulAction.mem_stabilizer_iff
    rw [e]
    exact isClosed_singleton.preimage hc
  haveI : IsClosed ((MulAction.stabilizer G x0 : Subgroup G) : Set G) := hS
  haveI : PolishSpace (G ⧸ MulAction.stabilizer G x0) := polish_of_lcsc _
  haveI : PolishSpace G := polish_of_lcsc G
  have hqc : Continuous (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) :=
    (QuotientGroup.isQuotientMap_mk _).continuous
  haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := by
    refine ⟨le_antisymm ?_ ?_⟩
    · intro A hA
      have hA' : MeasurableSet ((QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) ⁻¹' A) := hA
      have hAc' : MeasurableSet ((QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) ⁻¹' Aᶜ) :=
        hA'.compl
      letI : MeasurableSpace (G ⧸ MulAction.stabilizer G x0) := borel _
      haveI : BorelSpace (G ⧸ MulAction.stabilizer G x0) := ⟨rfl⟩
      have h1 : AnalyticSet A := by
        rw [← Set.image_preimage_eq A QuotientGroup.mk_surjective]
        exact hA'.analyticSet_image hqc.measurable
      have h2 : AnalyticSet Aᶜ := by
        rw [← Set.image_preimage_eq Aᶜ QuotientGroup.mk_surjective]
        exact hAc'.analyticSet_image hqc.measurable
      exact h1.measurableSet_of_compl h2
    · refine MeasurableSpace.generateFrom_le ?_
      intro U hU
      exact (hU.preimage hqc).measurableSet
  have hπ : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) :=
    (orb_cont x0 hc).measurableEmbedding (orb_inj x0)
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0) := by
    first
    | exact measurable_quotient_mk''
    | exact measurable_quotient_mk'
    | exact (QuotientGroup.continuous_mk).measurable
    | exact continuous_quot_mk.measurable
    | fun_prop
  have hmap : μ.map (fun g => g • x0) =
      (μ.map (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x0)).map
        (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
    rw [Measure.map_map hπ.measurable hmk]
    congr 1
    funext g
    exact (orb_mk x0 g).symm
  have hFs : ∀ q : G ⧸ MulAction.stabilizer G x0,
      ∫⁻ h', f (s (q.out • x0) * (h' : G)) ∂ν = ∫⁻ h', f (q.out * (h' : G)) ∂ν := by
    intro q
    have hy : s (q.out • x0) • x0 = q.out • x0 := hs _ ⟨q.out, rfl⟩
    have hk : (q.out)⁻¹ * s (q.out • x0) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hy, ← mul_smul, inv_mul_cancel, one_smul]
    have e : s (q.out • x0) = q.out * ((q.out)⁻¹ * s (q.out • x0)) := by group
    rw [e]
    exact avg_mul_mem (MulAction.stabilizer G x0) ν f q.out ⟨_, hk⟩
  have hinner : ∀ k : MulAction.stabilizer G x0, ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := fun k =>
    lintegral_mul_right_of_mem μ (MulAction.stabilizer G x0) ν h0 hfin k hf
  rw [hmap, hπ.lintegral_map]
  simp only [hFs]
  rw [lintegral_map (meas_avg_q (MulAction.stabilizer G x0) ν hf) hmk]
  simp only [avg_out]
  rw [lintegral_lintegral_swap (f := fun (g : G) (h : MulAction.stabilizer G x0) => f (g * (h : G)))
    ((hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).aemeasurable)]
  simp only [hinner, lintegral_const]
  rw [mul_comm (∫⁻ g, f g ∂μ), ← mul_assoc, ENNReal.inv_mul_cancel h0 hfin, one_mul]
end PI.AprimeInfA
