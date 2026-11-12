-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tResourceAxisAngle_irrational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:10:37.311064+00:00
-- url     : https://prove2.me/submissions/5cf12f8e-d5fe-4e35-b5cd-d93787f10828

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    Irrational (tResourceAxisAngle / (2 * Real.pi)) := by
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have hangle_rat : ∃ r : Rat, tResourceAxisAngle = r * Real.pi := by
    refine ⟨2 * q, ?_⟩
    calc
      tResourceAxisAngle =
          (tResourceAxisAngle / (2 * Real.pi)) * (2 * Real.pi) := by
            field_simp
      _ = (q : Real) * (2 * Real.pi) := by rw [hq]
      _ = ((2 * q : Rat) : Real) * Real.pi := by push_cast; ring
  have hcos_value : Real.cos tResourceAxisAngle = 3 / 4 := by
    rw [tResourceAxisAngle, Real.cos_arccos (by norm_num) (by norm_num)]
  have hcos : ∃ q : Rat, Real.cos tResourceAxisAngle = q := by
    refine ⟨3 / 4, ?_⟩
    norm_num at hcos_value ⊢
    exact hcos_value
  have hniven := niven hangle_rat hcos
  rw [hcos_value] at hniven
  norm_num at hniven
end QEC.Distillation.OneQubitMagic
