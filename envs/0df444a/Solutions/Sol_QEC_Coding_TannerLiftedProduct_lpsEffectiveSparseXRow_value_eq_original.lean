-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveSparseXRow_value_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:18:57.811993+00:00
-- url     : https://prove2.me/submissions/a7f07bb1-9783-4e24-996c-7b8b67e763be

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSparseXRow_value_eq
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
    (x : LPSSparseXIndex (lpsResiduePrimeSequence hp hp4 n).q D r)
    (qubit : LPSSparseQubitIndex (lpsResiduePrimeSequence hp hp4 n).q D r r') :
    lpsSparseRowValue (lpsEffectiveSparseXRow hp hp4 n generators h h' x) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) h h')
        (lpsSparseXDecode x) (lpsSparseQubitDecode qubit) := by
  have hLabel : (fun j => lpsEffectiveQuaternionFamilyLabel hp hp4 n (generators j)) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => congrFun (lpsEffectiveQuaternionFamilyLabel_eq_original hp hp4 n)
      (generators j))
  exact (lpsEffectiveSparseXRow_value_eq hp hp4 n generators h h' x qubit).trans
    (congrArg (fun label => LiftedProduct.boundary1Matrix (data label h h')
      (lpsSparseXDecode x) (lpsSparseQubitDecode qubit)) hLabel)
end QEC.Coding.TannerLiftedProduct
