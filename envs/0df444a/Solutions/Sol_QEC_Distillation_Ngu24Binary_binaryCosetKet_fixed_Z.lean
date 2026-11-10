-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCosetKet_fixed_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:57:03.495478+00:00
-- url     : https://prove2.me/submissions/b382dd22-e3f7-4eb6-885c-d52ff82af0a4

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssZCheck_apply_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (z : Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512))
    (hz : z ∈ (binaryZCode i).carrier) :
    PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck z)
      (binaryCosetKet i u) = binaryCosetKet i u := by
  unfold binaryCosetKet
  erw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [PauliSymplectic.cssZCheck_apply_basis]
  have hzero : wordPairing z (binaryCosetWordMap i (u, h)) = 0 :=
    ((binaryAmbientCode i).mem_dual z).mp hz _ ⟨(u, h), rfl⟩
  rw [hzero, PauliSymplectic.binaryPhaseScalar_zero, one_smul]
end QEC.Distillation.Ngu24Binary
