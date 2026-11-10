-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13_conjugates_x_on_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:45:18.436309+00:00
-- url     : https://prove2.me/submissions/db2e3f62-bc3a-4ff6-897c-af52e22b72a4

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_xTransport_apply_basis
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13Transport_symm_apply_basis
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13Transport_apply_basis
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p]
    (hp : PrimeAtLeastFive p) (x : ZMod p) :
    u13Transport p (xTransport p ((u13Transport p).symm (quditBasisKet p x))) =
      u13ConjugatedXAmplitude p x • quditBasisKet p (x + 1) := by
  have hp_nonzero : p ≠ 0 := hp.prime.ne_zero
  rw [u13Transport_symm_apply_basis,
    map_smul, xTransport_apply_basis, map_smul, u13Transport_apply_basis]
  unfold u13ConjugatedXAmplitude
  rw [smul_smul]
  change (phase p (-(x ^ 3)) * phase p ((x + 1) ^ 3)) • quditBasisKet p (x + 1) =
    phase p ((x + 1) ^ 3 - x ^ 3) • quditBasisKet p (x + 1)
  congr 1
  rw [← phase_add]
  ring
end QEC.Distillation.KT19PrimeQuditCSS
