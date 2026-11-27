-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_proof_514548fba2de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:41.188952+00:00
-- url     : https://prove2.me/submissions/6e9b3380-06cf-460c-aa1d-f48c55f056a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace MajorantTransport
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantTransport.Statement h v := by
  intro M
  have : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨d, S, hS⟩ := MajorantTransport.exists_isometry M
  set c := Measure.addHaarScalarFactor (Measure.map S.symm volume)
    (volume : Measure (InfinitePlace E → ι → ℂ))
  have hc : Measure.map S.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map S.symm volume) volume
  refine ⟨d, c, fun g => ⟨(MajorantTransport.invApplyEquiv g).trans S, fun y => hS _,
    fun L _ _ => ?_⟩⟩
  set T := (MajorantTransport.invApplyEquiv g).trans S
  have hT : MeasurePreserving T.symm volume (Measure.map T.symm volume) :=
    T.symm.continuous.measurable.measurePreserving _
  rw [ZLattice.covolume_comap L (Measure.map T.symm volume) volume hT]
  have hsymm : ⇑(MajorantTransport.invApplyEquiv g).symm = invApply g⁻¹ := rfl
  have hmap : Measure.map T.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) := by
    have hcomp : ⇑T.symm = (MajorantTransport.invApplyEquiv g).symm ∘ S.symm := rfl
    rw [hcomp, ← Measure.map_map (MajorantTransport.invApplyEquiv g).symm.continuous.measurable
      S.symm.continuous.measurable, hc, Measure.map_smul, hsymm,
      (MajorantTransport.measurePreserving_invApply g⁻¹).map_eq]
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L _ (ZLattice.isAddFundamentalDomain b _),
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), hmap, measureReal_nnreal_smul_apply]
end MajorantTransport
end GroundTheory.Heights₂.Heights.FiniteCovolume
