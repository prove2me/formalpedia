-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.centered_sum_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:55.024808+00:00
-- url     : https://prove2.me/submissions/57baacbf-185b-4e7a-ad83-aef59822238c

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Theorems.Thm_QEC_Distillation_FiniteCentering_finset_centered_sum_eq_nonzero_residual


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u v w
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (support : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι)
    (center raw residual : M) (mass : R)
    (hraw : raw = support.sum (fun i =>
      if accepts i then weight i • branch i else 0))
    (hmass : mass = support.sum (fun i =>
      if accepts i then weight i else 0))
    (hresidual : residual = support.sum (fun i =>
      if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0))
    (hzero : branch zeroIndex = center) :
    raw - mass • center = residual := by
  rw [hraw, hmass, hresidual]
  exact FiniteCentering.finset_centered_sum_eq_nonzero_residual
    support weight accepts branch zeroIndex center hzero
end QEC.Distillation.HH18Parameterized
