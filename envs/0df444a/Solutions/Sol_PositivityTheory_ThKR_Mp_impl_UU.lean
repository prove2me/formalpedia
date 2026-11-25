-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.impl_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:45.71594+00:00
-- url     : https://prove2.me/submissions/f5380d9f-00aa-4184-be9a-ba60868e9284

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_metaplectic_unipotent_block_first_diag
import Theorems.Thm_PositivityTheory_ThKR_Mp_metaplectic_unipotent_block_upper
import Theorems.Thm_PositivityTheory_ThKR_Mp_metaplectic_unipotent_block_lower
import Theorems.Thm_PositivityTheory_ThKR_Mp_metaplectic_unipotent_block_second_diag
import Theorems.Thm_PositivityTheory_ThKR_Mp_intw_UU
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_fou
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_fouInv
import Theorems.Thm_PositivityTheory_ThKR_LL_iso_ph
import Theorems.Thm_PositivityTheory_ThKR_LL_pPart_mulVec
import Theorems.Thm_PositivityTheory_ThKR_LL_qPart_mulVec
import Theorems.Thm_PositivityTheory_ThKR_LL_rhoFun_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) :
    Impl (fun w => nn S t *ᵥ w) (UU S t).toLinearMap :=
  ⟨fun f => (iso_fou.mul ((iso_ph _).mul iso_fouInv)) f, fun w f g hg => by
    have := intw_UU hS t (pPart w) (qPart w) f g hg
    rw [rhoFun_eq, pPart_mulVec, qPart_mulVec, metaplectic_unipotent_block_first_diag,
      metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metaplectic_unipotent_block_second_diag]
    simpa using this⟩
end PositivityTheory.ThKR.Mp
