-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply_of_reducedCombination_oddWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:36:42.017941+00:00
-- url     : https://prove2.me/submissions/17b19a9e-e644-46b0-85b6-6bfa4b7f4a81

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_phaseAmplitude_pi_div_four_eq_of_natCast_eq
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply_of_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalExponent8_eq_hammingWeight_oddCoefficients
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
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 * (HammingWeight (R.oddCoefficients c) : Real)) *
        psi bits := by
  rw [R.correctedAllSiteT_apply_of_reducedCombination hR psi bits c hbits]
  have hphase := phaseAmplitude_pi_div_four_eq_of_natCast_eq
    (HammingWeight (R.oddCoefficients c))
    (R.logicalExponent8 c R.reducedRowIndexList)
    (R.logicalExponent8_eq_hammingWeight_oddCoefficients c).symm
  rw [← hphase]
end QEC.Distillation.Triorthogonal.BinaryRowFamily
