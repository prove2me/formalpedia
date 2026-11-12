-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildResources_eq_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:37:10.659354+00:00
-- url     : https://prove2.me/submissions/5b203f39-15a2-4366-b1db-afba0be1ea1e

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoFreshParentPortDensity_eq_selectedPortDensity

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildResources q p port =
      noisyResources q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  funext parent
  change depthTwoFreshParentPortDensity q p parent port =
    OneQubit.diagonalAResource
      (bh12DecodedMarginalErrorParameter q p hsuccess port)
  rw [depthTwoFreshParentPortDensity_eq_selectedPortDensity]
  exact bh12SelectedPortTransportedDensity_eq_diagonalAResource q p hsuccess port
end QEC.Distillation.Triorthogonal.BH12Concatenation
