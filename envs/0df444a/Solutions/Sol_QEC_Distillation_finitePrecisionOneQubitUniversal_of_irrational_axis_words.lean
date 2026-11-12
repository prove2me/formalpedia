-- Prove2me | solution 1 for QEC.Distillation.finitePrecisionOneQubitUniversal_of_irrational_axis_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:40:35.368468+00:00
-- url     : https://prove2.me/submissions/a4825fd2-95e1-49cb-8c10-16fab2fd487b

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_projectivelyGeneratedDense_of_irrational_axis_words
import Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionOneQubitUniversal_of_projectivelyGeneratedDense


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
    FinitePrecisionOneQubitUniversal generators :=
  finitePrecisionOneQubitUniversal_of_projectivelyGeneratedDense
    (projectivelyGeneratedDense_of_irrational_axis_words generators axis axis' theta word word'
      hword hword_eq hword' hword'_eq htheta hnonparallel)
end QEC.Distillation
