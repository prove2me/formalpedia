-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_map_thetaT_eq_self_258ed7b78331
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:55.56088+00:00
-- url     : https://prove2.me/submissions/4a70d00b-0ec2-4efa-ade4-0c8c5bc89499

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_GL_9d991f300e31
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
open MapThetaTInvariant
open GroundTheory.Automorphic.ContragredientTranspose
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
    [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    Measure.map (⇑thetaT) μ = μ := by
  have := secondCountableTopology_GL (F := F) (n := n)
  set θ : GL (Fin n) F ≃ₜ* GL (Fin n) F := thetaTContinuous
  have hθ : ⇑(thetaT : GL (Fin n) F ≃* GL (Fin n) F) = ⇑θ := rfl
  have hmeas : Measurable θ := θ.continuous.measurable
  rw [hθ]
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map θ) μ
  set c := Measure.haarScalarFactor (μ.map θ) μ

  have h2 : (μ.map θ).map θ = μ := by
    rw [Measure.map_map hmeas hmeas]
    convert Measure.map_id
    ext g : 1
    exact thetaT_thetaT g
  have hsq : (c * c) • μ = μ := by
    conv_rhs => rw [← h2, hc, Measure.map_smul, hc, smul_smul]

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GL (Fin n) F)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hcc : c * c = 1 := by
    have := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) hsq
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    have h' : ((c * c : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact this
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact_mod_cast this
  have hc1 : c = 1 := by
    have h0 : (0 : NNReal) ≤ c := c.2
    nlinarith [mul_self_nonneg (c - 1)]
  rw [hc, hc1, one_smul]
end GroundTheory.Variant₂.N1
