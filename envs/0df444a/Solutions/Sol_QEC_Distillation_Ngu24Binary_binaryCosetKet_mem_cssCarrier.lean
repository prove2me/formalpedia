-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCosetKet_mem_cssCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:06:30.87397+00:00
-- url     : https://prove2.me/submissions/65aa4e18-c4a5-4eaa-bec8-deed489a8f49

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_fixed_X
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_fixed_Z

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryCosetKet i u ∈ (binaryCSSCode i).stabilizer.code.carrier := by
  change binaryCosetKet i u ∈
    (PauliSymplectic.binaryCSSQuantumCodeOfDualLe _ _ (binaryZCode_le_xDual i)).carrier
  rw [PauliSymplectic.mem_binaryCSSQuantumCodeOfDualLe_carrier]
  intro P hP
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · obtain ⟨k, rfl⟩ := hx
    exact binaryCosetKet_fixed_X i u k
  · exact binaryCosetKet_fixed_Z i u z hz
end QEC.Distillation.Ngu24Binary
