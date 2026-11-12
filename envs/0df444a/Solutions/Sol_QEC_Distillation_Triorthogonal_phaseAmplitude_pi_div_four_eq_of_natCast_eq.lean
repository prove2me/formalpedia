-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_of_natCast_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:49:56.465046+00:00
-- url     : https://prove2.me/submissions/74833c75-f5f8-4c6d-a4b8-5849a230195d

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (n : Nat) (e : ZMod 8) (h : (n : ZMod 8) = e) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (e.val : Real)) := by
  apply phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
  rw [h]
  exact (ZMod.natCast_zmod_val e).symm
end QEC.Distillation.Triorthogonal
