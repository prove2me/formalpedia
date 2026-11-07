-- Prove2me | solution 1 for QEC.Coding.f256SelectedCoordinates_ternary_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:43.901196+00:00
-- url     : https://prove2.me/submissions/2b4472b0-c1ce-44b6-97a0-32856bdb73fb

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Theorems.Thm_QEC_Coding_f256SelectorFunctional_eq_selected_sum
import Theorems.Thm_QEC_Coding_f256MFE_ternary_reverse_mul
import Theorems.Thm_QEC_Coding_f256SelectorFunctional_apply


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (x y z : F256) :
    (∑ q ∈ f256SelectedCoordinates,
      f256MFESigma x q * f256MFESigma y (f256MFEpi2 q) *
        f256MFESigma z (f256MFEpi3 q)) = f256RMFEpsi (x * y * z) := by
  have h := f256SelectorFunctional_eq_selected_sum
    (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
      f256MFEpi3Action (f256MFESigma z))
  rw [f256SelectorFunctional_apply, f256MFE_ternary_reverse_mul] at h
  exact h.symm
end QEC.Coding
