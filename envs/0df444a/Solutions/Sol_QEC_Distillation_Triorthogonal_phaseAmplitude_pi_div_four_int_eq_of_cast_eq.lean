-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_int_eq_of_cast_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:34:22.3622+00:00
-- url     : https://prove2.me/submissions/a28123ee-307b-427d-a55b-d84a74cf733f

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_two_pi_mul_int


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace QEC.Distillation.Triorthogonal
theorem _root_.solution
    (m n : Int) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by
  have hmod : m ≡ n [ZMOD (8 : Int)] :=
    (ZMod.intCast_eq_intCast_iff m n 8).mp h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hnm : n = m + 8 * k := by omega
  have hangle :
      Real.pi / 4 * (n : Real) =
        Real.pi / 4 * (m : Real) + (2 * Real.pi) * (k : Real) := by
    rw [hnm]
    push_cast
    ring
  rw [hangle, OneQubitMagic.phaseAmplitude_add,
    OneQubitMagic.phaseAmplitude_two_pi_mul_int, mul_one]
end QEC.Distillation.Triorthogonal
