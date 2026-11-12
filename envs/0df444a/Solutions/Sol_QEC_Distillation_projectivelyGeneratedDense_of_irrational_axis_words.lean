-- Prove2me | solution 1 for QEC.Distillation.projectivelyGeneratedDense_of_irrational_axis_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:38:35.853461+00:00
-- url     : https://prove2.me/submissions/7fc8ac10-63f9-45f3-a9e9-36cacb53eb46

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_isClosed_specialUnitaryGeneratedClosure
import Theorems.Thm_QEC_Distillation_axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_globalPhaseEquivalent_symm
import Theorems.Thm_QEC_Distillation_closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
import Theorems.Thm_QEC_Distillation_phaseNormalize_det
import Theorems.Thm_QEC_Distillation_phaseNormalize_globalPhaseEquivalent


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution
    (generators : Set SingleQubitGate) (axis axis' : UnitBlochAxis) (theta : ℝ)
    (word word' : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (hword' : word' ∈ generatedUnitarySubgroup generators)
    (hword'_eq : word' = axisCircle axis' (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi)))
    (hnonparallel : axis.Nonparallel axis') :
    ProjectivelyGeneratedDense generators := by
  let K := specialUnitaryGeneratedClosure generators
  have haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K := by
    exact axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      generators axis theta word hword hword_eq htheta
  have haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K := by
    exact axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      generators axis' theta word' hword' hword'_eq htheta
  have htop : K = ⊤ :=
    closedSubgroup_eq_top_of_contains_nonparallel_axisCircles K
      (isClosed_specialUnitaryGeneratedClosure generators) axis axis' hnonparallel haxis haxis'
  intro target
  refine ⟨phaseNormalize target, ?_, ?_⟩
  · change (⟨phaseNormalize target, phaseNormalize_det target⟩ :
      SingleQubitSpecialUnitary) ∈ K
    rw [htop]
    trivial
  · exact globalPhaseEquivalent_symm (phaseNormalize_globalPhaseEquivalent target)
end QEC.Distillation
