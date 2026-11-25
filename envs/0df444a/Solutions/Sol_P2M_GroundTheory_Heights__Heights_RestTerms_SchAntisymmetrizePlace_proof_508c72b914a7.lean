-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchAntisymmetrizePlace_proof_508c72b914a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:25.184801+00:00
-- url     : https://prove2.me/submissions/603494bc-ade9-4055-9398-3c04a43da30c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAntisymmetrizePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchAntisymmetrizePlace
theorem _root_.solution : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym
  rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp only [Function.comp_apply, smallBlockPlace_eq, Equiv.permCongr_apply, Equiv.symm_symm]
  rw [← he]
  simp
end SchAntisymmetrizePlace
end GroundTheory.Heights₂.Heights.RestTerms
