-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.phaseAmplitude_pi_div_four_eq_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:26:36.902424+00:00
-- url     : https://prove2.me/submissions/09f68a7e-f729-4ea5-8918-6b4bb8c2ab47

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
theorem _root_.solution (n : Nat) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * ((n : ZMod 8).val : Real)) := by
  apply phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
  exact (ZMod.natCast_zmod_val (n : ZMod 8)).symm
end QEC.Distillation.Triorthogonal
