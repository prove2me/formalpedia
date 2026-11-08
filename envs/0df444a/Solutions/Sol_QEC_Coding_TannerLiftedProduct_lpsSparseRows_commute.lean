-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSparseRows_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:58:05.632034+00:00
-- url     : https://prove2.me/submissions/4f4f0ab6-76be-42d7-aef3-22978ccee5ef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseXRow_value_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZRow_value_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseQubitEquiv_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex q D r) (z : LPSSparseZIndex q D r') :
    ∑ qubit : LPSSparseQubitIndex q D r r',
      lpsSparseRowValue (lpsSparseXRow label h h' x) qubit *
        lpsSparseRowValue (lpsSparseZRow label h h' z) qubit = 0 := by
  classical
  simp_rw [lpsSparseXRow_value_eq, lpsSparseZRow_value_eq, ← lpsSparseQubitEquiv_apply]
  calc
    _ = ∑ y, LiftedProduct.boundary1Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseXDecode x) y * LiftedProduct.boundary2Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        y (lpsSparseZDecode z) := lpsSparseQubitEquiv.sum_comp _
    _ = 0 := congrFun (congrFun
    (LiftedProduct.boundary1Matrix_mul_boundary2Matrix
      (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h'))
    (lpsSparseXDecode x)) (lpsSparseZDecode z)
end QEC.Coding.TannerLiftedProduct
