-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13_has_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:48:46.673197+00:00
-- url     : https://prove2.me/submissions/a30ccaf7-f833-4b5a-9424-7a2b3fa87dad

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedXExponent_eq_quadratic
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_six_ne_zero
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedX_firstDifference_is_pauli
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedX_firstDifference_is_pauli_on_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] (hp : PrimeAtLeastFive p) :
    U13HierarchyWitness p :=
  ⟨u13ConjugatedXExponent_eq_quadratic p,
    u13ConjugatedX_firstDifference_is_pauli p,
    u13ConjugatedX_firstDifference_is_pauli_on_basis p, six_ne_zero p hp⟩
end QEC.Distillation.KT19PrimeQuditCSS
