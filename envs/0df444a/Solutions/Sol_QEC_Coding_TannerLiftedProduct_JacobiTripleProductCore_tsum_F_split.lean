-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:00.319894+00:00
-- url     : https://prove2.me/submissions/503e1b53-7c80-4380-89ac-25c226422225

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_summable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' (p : ℤ × ℕ), F p) =
    (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) +
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) := by
  letI : UniformSpace R := piUnif
  haveI : IsUniformAddGroup R := PowerSeries.WithPiTopology.instIsUniformAddGroup _
  haveI : CompleteSpace R := PowerSeries.WithPiTopology.instCompleteSpace _
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  have hsumm : Summable (fun p : ℤ × ℕ ↦ F p) := by
    rw [show piUnif.toTopologicalSpace = piTop from rfl,
      PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    exact coeff_F_summable
  exact (hsumm.tsum_subtype_add_tsum_subtype_compl {p | 0 ≤ p.1}).symm
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
