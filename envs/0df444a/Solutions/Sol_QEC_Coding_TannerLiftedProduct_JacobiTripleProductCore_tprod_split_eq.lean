-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tprod_split_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:26.683916+00:00
-- url     : https://prove2.me/submissions/744e25b6-c39a-4bf5-96fb-994740b68649

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_shift_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_shifted

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    (∏' n, (1 - q ^ 2 * (q ^ 2) ^ n)) =
    (∏ i ∈ Finset.range k, (1 - q ^ 2 * (q ^ 2) ^ i)) *
    (∏' n, (1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n)) := by
  letI := piTop
  have hT2 : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  have hCM : ContinuousMul R := instIsTopologicalSemiringPiTop.toContinuousMul
  have hshift : Multipliable (fun n ↦ (1 : R) - q ^ 2 * (q ^ 2) ^ (n + k)) :=
    (multipliable_shifted k).congr (fun n ↦ (factor_shift_eq n k).symm)
  have key := @Multipliable.prod_mul_tprod_nat_mul' R _ _ hT2 hCM
    (f := fun n ↦ 1 - q ^ 2 * (q ^ 2) ^ n) (k := k) hshift
  calc
    (∏' n, (1 - q ^ 2 * (q ^ 2) ^ n)) =
        (∏ i ∈ Finset.range k, (1 - q ^ 2 * (q ^ 2) ^ i)) *
          (∏' n, (1 - q ^ 2 * (q ^ 2) ^ (n + k))) := key.symm
    _ = _ := congrArg
      (fun z => (∏ i ∈ Finset.range k, (1 - q ^ 2 * (q ^ 2) ^ i)) * z)
      (tprod_congr (fun n ↦ factor_shift_eq n k))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
