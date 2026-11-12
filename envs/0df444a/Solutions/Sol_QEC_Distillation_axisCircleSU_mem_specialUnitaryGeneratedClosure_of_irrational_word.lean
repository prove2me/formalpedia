-- Prove2me | solution 1 for QEC.Distillation.axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:21:20.571617+00:00
-- url     : https://prove2.me/submissions/d7c30cc5-c4cc-4a46-9c56-3ce7c3c7eb2e

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_isClosed_specialUnitaryGeneratedClosure
import Theorems.Thm_QEC_Distillation_axisCircleSU_zsmul
import Theorems.Thm_QEC_Distillation_continuous_axisCircleSU

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution
    (generators : Set SingleQubitGate) (axis : UnitBlochAxis) (theta : ℝ)
    (word : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi))) :
    ∀ t : AddCircle (2 * Real.pi),
      axisCircleSU axis t ∈ specialUnitaryGeneratedClosure generators := by
  let K := specialUnitaryGeneratedClosure generators
  have hbase : axisCircleSU axis (theta : AddCircle (2 * Real.pi)) ∈ K := by
    change axisCircle axis (theta : AddCircle (2 * Real.pi)) ∈
      (generatedUnitarySubgroup generators).topologicalClosure
    rw [← hword_eq]
    exact Subgroup.le_topologicalClosure _ hword
  have hclosed : IsClosed (K : Set SingleQubitSpecialUnitary) := by
    exact isClosed_specialUnitaryGeneratedClosure generators
  have horbit : Set.range (fun z : Int => z • (theta : AddCircle (2 * Real.pi))) ⊆
      (axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary) := by
    rintro _ ⟨z, rfl⟩
    change axisCircleSU axis (z • (theta : AddCircle (2 * Real.pi))) ∈ K
    rw [axisCircleSU_zsmul]
    exact K.zpow_mem hbase z
  have hpreimage : IsClosed ((axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary)) :=
    hclosed.preimage (continuous_axisCircleSU axis)
  have hclosure : closure (Set.range (fun z : Int =>
      z • (theta : AddCircle (2 * Real.pi)))) ⊆
      (axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary) :=
    closure_minimal horbit hpreimage
  have hdense : DenseRange (fun z : Int => z • (theta : AddCircle (2 * Real.pi))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr htheta
  intro t
  apply hclosure
  rw [dense_iff_closure_eq.mp hdense]
  trivial
end QEC.Distillation
