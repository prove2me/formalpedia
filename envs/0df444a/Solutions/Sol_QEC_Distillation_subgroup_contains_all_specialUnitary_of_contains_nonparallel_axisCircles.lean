-- Prove2me | solution 1 for QEC.Distillation.subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:34:02.812505+00:00
-- url     : https://prove2.me/submissions/a77a86b2-5227-4b93-b712-68e82851be97

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_subgroup_isOpen_of_contains_nonparallel_axisCircles

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
theorem _root_.solution
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (U : SingleQubitSpecialUnitary) : U ∈ K := by
  have hopen : IsOpen (K : Set SingleQubitSpecialUnitary) :=
    subgroup_isOpen_of_contains_nonparallel_axisCircles K axis axis'
      hnonparallel haxis haxis'
  have hclopen : IsClopen (K : Set SingleQubitSpecialUnitary) :=
    ⟨Subgroup.isClosed_of_isOpen K hopen, hopen⟩
  let gamma := specialUnitaryPath U
  have hpreconnected : IsPreconnected (Set.range gamma) :=
    isPreconnected_range gamma.continuous
  have hrange : Set.range gamma ⊆ K :=
    hpreconnected.subset_isClopen hclopen
      ⟨1, ⟨0, gamma.source⟩, K.one_mem⟩
  exact hrange ⟨1, gamma.target⟩
end QEC.Distillation
