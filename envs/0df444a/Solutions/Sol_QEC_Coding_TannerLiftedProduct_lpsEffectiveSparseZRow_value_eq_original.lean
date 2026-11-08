-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseZRow_value_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:18:59.702962+00:00
-- url     : https://prove2.me/submissions/5228e427-51b3-453e-a7f4-d3277112e45b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseZRow_value_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq_original


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p D r r' : ℕ}
    {F : Type} [Field F] [Fintype F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsResiduePrimeSequence hp hp4 n).q D r')
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseZRow hp hp4 n generators h h' z) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode z) := by
  have hLabel : (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n)
      (generators j))
  exact (lpsEffectiveSparseZRow_value_eq hp hp4 n generators h h' z qubit).trans
    (congrArg (fun label => LiftedProduct.boundary2Matrix (data label h h')
      (lpsSparseQubitDecode qubit) (lpsSparseZDecode z)) hLabel)
end QEC.Coding.TannerLiftedProduct
