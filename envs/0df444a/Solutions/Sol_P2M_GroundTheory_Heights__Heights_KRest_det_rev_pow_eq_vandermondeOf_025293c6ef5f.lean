-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:55.735869+00:00
-- url     : https://prove2.me/submissions/2a941764-0b96-4538-9c09-44abe58aeb11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det = RestTerms.vandermondeOf v := by
  have h1 : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det =
      (Matrix.vandermonde (v ∘ Fin.rev)).det := by
    rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
      (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ)))]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply,
      Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    have := b.isLt
    omega
  rw [h1, Matrix.det_vandermonde, RestTerms.vandermondeOf, prod_Ioi_eq_prod_ite,
    prod_Ioi_eq_prod_ite]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Fin.rev_lt_rev, Function.comp_apply]
end GroundTheory.Heights₂.Heights.KRest
